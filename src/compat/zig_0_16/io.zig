const std = @import("std");

pub const Context = struct {
    threaded: std.Io.Threaded,
    thread_count: usize,

    pub fn init(allocator: std.mem.Allocator, thread_count: usize) !Context {
        const effective_thread_count = @max(1, thread_count);
        return .{
            .threaded = .init(allocator, .{
                // Io.async also runs work eagerly on the calling thread.
                .async_limit = .limited(effective_thread_count - 1),
                .concurrent_limit = .limited(effective_thread_count),
            }),
            .thread_count = effective_thread_count,
        };
    }

    pub fn deinit(self: *Context) void {
        self.threaded.deinit();
    }

    pub fn io(self: *Context) std.Io {
        return self.threaded.io();
    }
};

var default_context: Context = .{
    .threaded = .init_single_threaded,
    .thread_count = 1,
};

pub fn defaultContext() *Context {
    return &default_context;
}

pub const TaskFn = *const fn (usize, *anyopaque) void;

const PendingTask = struct {
    function: TaskFn,
    index: usize,
    context: *anyopaque,
};

fn runTask(task: PendingTask) void {
    task.function(task.index, task.context);
}

pub const Executor = struct {
    context: *Context,
    group: std.Io.Group = .init,

    /// The context must outlive the executor and use the same normalized worker count.
    pub fn init(context: *Context, _: std.mem.Allocator, thread_count: usize) !Executor {
        if (@max(1, thread_count) != context.thread_count) return error.ThreadCountMismatch;
        return .{ .context = context };
    }

    pub fn deinit(self: *Executor) void {
        const io = self.context.io();
        // Group.await drains every task even when canceled. Re-arm cancellation
        // because this void cleanup method cannot return the cancellation error.
        self.group.await(io) catch |err| switch (err) {
            error.Canceled => io.recancel(),
        };
    }

    pub fn spawn(self: *Executor, function: TaskFn, index: usize, context: *anyopaque) !void {
        self.group.async(self.context.io(), runTask, .{PendingTask{
            .function = function,
            .index = index,
            .context = context,
        }});
    }

    pub fn wait(self: *Executor) !void {
        try self.group.await(self.context.io());
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
    // Zero and one both mean one worker, including the calling thread.
    for ([_][2]usize{ .{ 1, 1 }, .{ 0, 1 }, .{ 1, 0 } }) |counts| {
        var context = try Context.init(std.testing.allocator, counts[0]);
        defer context.deinit();
        var executor = try Executor.init(&context, std.testing.allocator, counts[1]);
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

test "Executor rejects both thread count mismatch directions" {
    for ([_][2]usize{ .{ 2, 1 }, .{ 1, 2 } }) |counts| {
        var context = try Context.init(std.testing.allocator, counts[0]);
        defer context.deinit();
        try std.testing.expectError(
            error.ThreadCountMismatch,
            Executor.init(&context, std.testing.allocator, counts[1]),
        );
    }
}

test "Executor deinit drains active work on early exit and preserves cancellation" {
    const Probe = struct {
        context: *Context,
        owner_ready: std.Io.Event = .unset,
        task_started: std.Io.Event = .unset,
        owner_blocked: std.Io.Event = .unset,
        task_blocked: std.Io.Event = .unset,
        task_completed: std.atomic.Value(bool) = .init(false),
        task_canceled: std.atomic.Value(bool) = .init(false),

        const Result = struct {
            completed_at_deinit: bool,
            task_canceled: bool,
            cancellation_preserved: bool,
            early_error_preserved: bool,
        };

        fn task(_: usize, opaque_context: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context));
            const io = self.context.io();
            self.task_started.set(io);
            self.task_blocked.wait(io) catch |err| switch (err) {
                error.Canceled => self.task_canceled.store(true, .release),
            };
            self.task_completed.store(true, .release);
        }

        fn leaveEarly(executor: *Executor) error{EarlyExit}!void {
            defer executor.deinit();
            return error.EarlyExit;
        }

        fn owner(self: *@This()) !Result {
            const io = self.context.io();
            defer self.owner_ready.set(io);
            var executor = try Executor.init(self.context, std.testing.allocator, 2);
            // Keep the regression safe even if deinit incorrectly returns early.
            defer executor.group.cancel(io);
            // Force concurrency: Group.async may otherwise run the blocked task eagerly.
            try executor.group.concurrent(io, task, .{
                @as(usize, 0),
                @as(*anyopaque, @ptrCast(self)),
            });
            self.task_started.waitUncancelable(io);
            self.owner_ready.set(io);
            self.owner_blocked.wait(io) catch |err| switch (err) {
                error.Canceled => io.recancel(),
            };

            const early_error_preserved = if (leaveEarly(&executor)) |_| false else |err| switch (err) {
                error.EarlyExit => true,
            };
            const completed_at_deinit = self.task_completed.load(.acquire);
            const task_canceled = self.task_canceled.load(.acquire);
            const cancellation_preserved = if (io.checkCancel()) |_| false else |err| switch (err) {
                error.Canceled => true,
            };
            return .{
                .completed_at_deinit = completed_at_deinit,
                .task_canceled = task_canceled,
                .cancellation_preserved = cancellation_preserved,
                .early_error_preserved = early_error_preserved,
            };
        }
    };
    var context = try Context.init(std.testing.allocator, 2);
    defer context.deinit();
    const io = context.io();
    var probe: Probe = .{ .context = &context };
    var owner = try io.concurrent(Probe.owner, .{&probe});
    probe.owner_ready.waitUncancelable(io);
    const result = try owner.cancel(io);
    try std.testing.expect(result.completed_at_deinit);
    try std.testing.expect(result.task_canceled);
    try std.testing.expect(result.cancellation_preserved);
    try std.testing.expect(result.early_error_preserved);
}

pub const Mutex = std.Io.Mutex;

pub fn initMutex() Mutex {
    return .init;
}

pub fn lockMutex(mutex: *Mutex, context: *Context) !void {
    try mutex.lock(context.io());
}

pub fn unlockMutex(mutex: *Mutex, context: *Context) void {
    mutex.unlock(context.io());
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
    dir: std.Io.Dir,
    iterator: ?std.Io.Dir.Iterator = null,
};

pub fn openDir(context: *Context, path: []const u8, iterate: bool) !Directory {
    const dir = if (std.fs.path.isAbsolute(path))
        try std.Io.Dir.openDirAbsolute(context.io(), path, .{ .iterate = iterate })
    else
        try std.Io.Dir.cwd().openDir(context.io(), path, .{ .iterate = iterate });
    return .{
        .dir = dir,
    };
}

pub fn closeDir(context: *Context, directory: *Directory) void {
    directory.dir.close(context.io());
}

pub fn nextDir(context: *Context, directory: *Directory) !?DirectoryEntry {
    if (directory.iterator == null) {
        const iterator: std.Io.Dir.Iterator = directory.dir.iterate();
        directory.iterator = iterator;
    }
    const entry = try directory.iterator.?.next(context.io()) orelse return null;
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
    context: *Context,
    allocator: std.mem.Allocator,
    path: []const u8,
    max_size: usize,
) ![:0]u8 {
    if (std.fs.path.isAbsolute(path)) {
        var file = try std.Io.Dir.openFileAbsolute(context.io(), path, .{});
        defer file.close(context.io());
        var reader = file.reader(context.io(), &.{});
        return reader.interface.allocRemainingAlignedSentinel(
            allocator,
            std.Io.Limit.limited(max_size),
            .of(u8),
            0,
            // The reader exposes the underlying failure through `reader.err`.
            // zwanzig-disable-next-line: swallowed-error
        ) catch |err| switch (err) {
            error.ReadFailed => blk: {
                std.debug.assert(reader.err != null);
                break :blk reader.err.?;
            },
            error.OutOfMemory, error.StreamTooLong => |e| e,
        };
    }

    return std.Io.Dir.cwd().readFileAllocOptions(
        context.io(),
        path,
        allocator,
        std.Io.Limit.limited(max_size),
        .of(u8),
        0,
    );
}

pub fn writeFile(context: *Context, path: []const u8, data: []const u8) !void {
    var file = if (std.fs.path.isAbsolute(path))
        try std.Io.Dir.createFileAbsolute(context.io(), path, .{})
    else
        try std.Io.Dir.cwd().createFile(context.io(), path, .{});
    defer file.close(context.io());
    try file.writeStreamingAll(context.io(), data);
}

pub fn makePath(context: *Context, path: []const u8) !void {
    try std.Io.Dir.cwd().createDirPath(context.io(), path);
}

pub fn deleteFile(context: *Context, path: []const u8) !void {
    if (std.fs.path.isAbsolute(path)) {
        return std.Io.Dir.deleteFileAbsolute(context.io(), path);
    }
    return std.Io.Dir.cwd().deleteFile(context.io(), path);
}

pub fn deleteTree(context: *Context, path: []const u8) !void {
    if (std.fs.path.isAbsolute(path)) {
        return std.Io.Dir.cwd().deleteTree(context.io(), path);
    }
    return std.Io.Dir.cwd().deleteTree(context.io(), path);
}

pub fn stat(context: *Context, path: []const u8) !EntryKind {
    const result = try std.Io.Dir.cwd().statFile(context.io(), path, .{});
    return switch (result.kind) {
        .file => .file,
        .directory => .directory,
        else => .other,
    };
}

pub const OutputWriter = struct {
    context: *Context,
    file: std.Io.File,
    file_writer: std.Io.File.Writer,
    buffer: [4096]u8,

    pub fn init(self: *OutputWriter, context: *Context, stderr: bool) void {
        self.context = context;
        self.file = if (stderr) std.Io.File.stderr() else std.Io.File.stdout();
        self.file_writer = self.file.writer(context.io(), &self.buffer);
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
        const path_len = inner.dir.realPath(std.testing.io, &path_buffer) catch @panic("failed to resolve test directory");
        return .{
            .inner = inner,
            .path_buffer = path_buffer,
            .path_len = path_len,
        };
    }

    pub fn path(self: *const TestDir) []const u8 {
        return self.path_buffer[0..self.path_len];
    }

    pub fn writeFile(self: *TestDir, name: []const u8, data: []const u8) !void {
        try self.inner.dir.writeFile(std.testing.io, .{ .sub_path = name, .data = data });
    }

    pub fn cleanup(self: *TestDir) void {
        self.inner.cleanup();
    }
};

pub fn timestamp(context: *Context) i64 {
    return std.Io.Clock.real.now(context.io()).toSeconds();
}
