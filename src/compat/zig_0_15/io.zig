const std = @import("std");

pub const Context = struct {
    // Keep this non-zero-sized: callers pass the context by pointer to both
    // version-specific implementations.
    marker: u8 = 0,

    pub fn init(_: std.mem.Allocator, _: usize) !Context {
        return .{};
    }

    pub fn deinit(_: *Context) void {}
};

var default_context: Context = .{};

pub fn defaultContext() *Context {
    return &default_context;
}

pub const TaskFn = *const fn (usize, *anyopaque) void;

const PendingTask = struct {
    function: TaskFn,
    index: usize,
    context: *anyopaque,
    wait_group: *std.Thread.WaitGroup,
};

fn runTask(task: PendingTask) void {
    defer task.wait_group.finish();
    task.function(task.index, task.context);
}

pub const Executor = struct {
    allocator: std.mem.Allocator,
    pool: ?*std.Thread.Pool,
    wait_group: std.Thread.WaitGroup,

    pub fn init(_: *Context, allocator: std.mem.Allocator, thread_count: usize) !Executor {
        const effective_thread_count = @max(1, thread_count);
        if (effective_thread_count == 1) {
            return .{ .allocator = allocator, .pool = null, .wait_group = .{} };
        }
        const pool = try allocator.create(std.Thread.Pool);
        errdefer allocator.destroy(pool);
        try pool.init(.{
            .allocator = allocator,
            // waitAndWork contributes the calling thread.
            .n_jobs = effective_thread_count - 1,
            .track_ids = true,
        });
        return .{
            .allocator = allocator,
            .pool = pool,
            .wait_group = .{},
        };
    }

    pub fn deinit(self: *Executor) void {
        const pool = self.pool orelse return;
        // Early exits must supply the caller's worker slot before joining the pool.
        pool.waitAndWork(&self.wait_group);
        pool.deinit();
        self.allocator.destroy(pool);
    }

    pub fn spawn(self: *Executor, function: TaskFn, index: usize, context: *anyopaque) !void {
        const pool = self.pool orelse {
            function(index, context);
            return;
        };
        self.wait_group.start();
        pool.spawn(runTask, .{PendingTask{
            .function = function,
            .index = index,
            .context = context,
            .wait_group = &self.wait_group,
        }}) catch |err| {
            self.wait_group.finish();
            return err;
        };
    }

    pub fn wait(self: *Executor) !void {
        const pool = self.pool orelse return;
        pool.waitAndWork(&self.wait_group);
        // waitAndWork can leave the waiting bit set; later wait/deinit calls must be safe.
        self.wait_group.reset();
    }
};

test "Executor respects a single analysis worker" {
    const Probe = struct {
        caller_id: std.Thread.Id,
        used_background_worker: std.atomic.Value(bool) = .init(false),
        completed: std.atomic.Value(usize) = .init(0),

        fn task(_: usize, opaque_context: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context));
            if (std.Thread.getCurrentId() != self.caller_id) {
                self.used_background_worker.store(true, .release);
            }
            _ = self.completed.fetchAdd(1, .release);
        }
    };
    for ([_]usize{ 0, 1 }) |thread_count| {
        var context = try Context.init(std.testing.allocator, thread_count);
        defer context.deinit();
        var executor = try Executor.init(&context, std.testing.allocator, thread_count);
        defer executor.deinit();
        var probe: Probe = .{ .caller_id = std.Thread.getCurrentId() };
        for (0..8) |index| {
            try executor.spawn(Probe.task, index, &probe);
            try std.testing.expectEqual(index + 1, probe.completed.load(.acquire));
        }
        try executor.wait();
        try std.testing.expect(!probe.used_background_worker.load(.acquire));
    }
}

test "Executor deinit drains with at most two workers including the caller" {
    if (@import("builtin").single_threaded) return error.SkipZigTest;
    const Probe = struct {
        caller_id: std.Thread.Id,
        started: std.Thread.ResetEvent = .{},
        mutex: std.Thread.Mutex = .{},
        condition: std.Thread.Condition = .{},
        arrived: usize = 0,
        active: usize = 0,
        peak: usize = 0,
        completed: usize = 0,
        caller_participated: bool = false,
        release_all: bool = false,

        fn task(index: usize, opaque_context: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context));
            self.mutex.lock();
            defer self.mutex.unlock();
            self.active += 1;
            self.peak = @max(self.peak, self.active);
            self.caller_participated = self.caller_participated or
                std.Thread.getCurrentId() == self.caller_id;
            const pair = self.arrived / 2;
            self.arrived += 1;
            if (index == 0) self.started.set();
            // Pair tasks without sleeps so teardown must supply the second worker.
            if (self.arrived % 2 == 0) {
                self.condition.broadcast();
            } else {
                while (!self.release_all and self.arrived / 2 == pair) {
                    self.condition.wait(&self.mutex);
                }
            }
            self.active -= 1;
            self.completed += 1;
        }
    };
    for ([_]bool{ false, true }) |wait_before_deinit| {
        var context = try Context.init(std.testing.allocator, 2);
        defer context.deinit();
        var probe: Probe = .{ .caller_id = std.Thread.getCurrentId() };
        {
            var executor = try Executor.init(&context, std.testing.allocator, 2);
            defer executor.deinit();
            errdefer {
                probe.mutex.lock();
                probe.release_all = true;
                probe.condition.broadcast();
                probe.mutex.unlock();
            }
            try executor.spawn(Probe.task, 0, &probe);
            probe.started.wait();
            for (1..8) |index| try executor.spawn(Probe.task, index, &probe);
            if (wait_before_deinit) {
                try executor.wait();
                try executor.wait();
            }
        }
        try std.testing.expectEqual(@as(usize, 8), probe.completed);
        try std.testing.expectEqual(@as(usize, 2), probe.peak);
        try std.testing.expect(probe.caller_participated);
    }
}

test "Executor deinit drains submitted tasks without wait" {
    const Task = struct {
        fn run(_: usize, opaque_context: *anyopaque) void {
            const completed: *std.atomic.Value(usize) = @ptrCast(@alignCast(opaque_context));
            _ = completed.fetchAdd(1, .release);
        }
    };
    for ([_]usize{ 0, 1, 2 }) |thread_count| {
        var context = try Context.init(std.testing.allocator, thread_count);
        defer context.deinit();
        var completed: std.atomic.Value(usize) = .init(0);
        {
            var executor = try Executor.init(&context, std.testing.allocator, thread_count);
            defer executor.deinit();
            for (0..8) |index| try executor.spawn(Task.run, index, &completed);
        }
        try std.testing.expectEqual(@as(usize, 8), completed.load(.acquire));
    }
}

pub const Mutex = std.Thread.Mutex;

pub fn initMutex() Mutex {
    return .{};
}

pub fn lockMutex(mutex: *Mutex, _: *Context) !void {
    mutex.lock();
}

pub fn unlockMutex(mutex: *Mutex, _: *Context) void {
    mutex.unlock();
}

pub const EntryKind = enum {
    file,
    directory,
    other,
};

pub const DirectoryEntry = struct {
    name: []const u8,
    kind: EntryKind,
};

pub const Directory = struct {
    dir: std.fs.Dir,
    iterator: ?std.fs.Dir.Iterator = null,
};

pub fn openDir(_: *Context, path: []const u8, iterate: bool) !Directory {
    return .{
        .dir = try std.fs.cwd().openDir(path, .{ .iterate = iterate }),
    };
}

pub fn closeDir(_: *Context, directory: *Directory) void {
    directory.dir.close();
}

pub fn nextDir(_: *Context, directory: *Directory) !?DirectoryEntry {
    if (directory.iterator == null) {
        const iterator: std.fs.Dir.Iterator = directory.dir.iterate();
        directory.iterator = iterator;
    }
    const entry = try directory.iterator.?.next() orelse return null;
    return .{
        .name = entry.name,
        .kind = switch (entry.kind) {
            .file => .file,
            .directory => .directory,
            else => .other,
        },
    };
}

pub fn readFileAlloc(
    _: *Context,
    allocator: std.mem.Allocator,
    path: []const u8,
    max_size: usize,
) ![:0]u8 {
    const file = if (std.fs.path.isAbsolute(path))
        try std.fs.openFileAbsolute(path, .{})
    else
        try std.fs.cwd().openFile(path, .{});
    defer file.close();

    return file.readToEndAllocOptions(
        allocator,
        max_size,
        null,
        std.mem.Alignment.of(u8),
        0,
    );
}

pub fn writeFile(_: *Context, path: []const u8, data: []const u8) !void {
    const file = if (std.fs.path.isAbsolute(path))
        try std.fs.createFileAbsolute(path, .{})
    else
        try std.fs.cwd().createFile(path, .{});
    defer file.close();
    try file.writeAll(data);
}

pub fn makePath(_: *Context, path: []const u8) !void {
    try std.fs.cwd().makePath(path);
}

pub fn deleteFile(_: *Context, path: []const u8) !void {
    if (std.fs.path.isAbsolute(path)) {
        return std.fs.deleteFileAbsolute(path);
    }
    return std.fs.cwd().deleteFile(path);
}

pub fn deleteTree(_: *Context, path: []const u8) !void {
    if (std.fs.path.isAbsolute(path)) {
        return std.fs.deleteTreeAbsolute(path);
    }
    return std.fs.cwd().deleteTree(path);
}

pub fn stat(_: *Context, path: []const u8) !EntryKind {
    const result = try std.fs.cwd().statFile(path);
    return switch (result.kind) {
        .file => .file,
        .directory => .directory,
        else => .other,
    };
}

pub const OutputWriter = struct {
    file: std.fs.File,
    file_writer: std.fs.File.Writer,
    buffer: [4096]u8,

    pub fn init(self: *OutputWriter, _: *Context, stderr: bool) void {
        self.file = if (stderr) std.fs.File.stderr() else std.fs.File.stdout();
        self.file_writer = self.file.writer(&self.buffer);
    }

    pub fn writer(self: *OutputWriter) *std.Io.Writer {
        return &self.file_writer.interface;
    }

    pub fn flush(self: *OutputWriter) std.Io.Writer.Error!void {
        try self.file_writer.interface.flush();
    }

    pub fn deinit(self: *OutputWriter) void {
        _ = self;
    }
};

pub const TestDir = struct {
    inner: std.testing.TmpDir,
    path_buffer: [std.fs.max_path_bytes]u8,
    path_len: usize,

    pub fn init() TestDir {
        var inner = std.testing.tmpDir(.{});
        var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const resolved_path = inner.dir.realpath(".", &path_buffer) catch @panic("failed to resolve test directory");
        return .{
            .inner = inner,
            .path_buffer = path_buffer,
            .path_len = resolved_path.len,
        };
    }

    pub fn path(self: *const TestDir) []const u8 {
        return self.path_buffer[0..self.path_len];
    }

    pub fn writeFile(self: *TestDir, name: []const u8, data: []const u8) !void {
        try self.inner.dir.writeFile(.{ .sub_path = name, .data = data });
    }

    pub fn cleanup(self: *TestDir) void {
        self.inner.cleanup();
    }
};

pub fn timestamp(_: *Context) i64 {
    return std.time.timestamp();
}
