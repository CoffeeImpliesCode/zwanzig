// EXPECT: line=22 rule=optional-unwrap severity=warning
//
// A method is the container that declares it together with the declaration
// itself, so two containers may carry the same name without either call
// reaching the other. The owner reaches its reducer through a typed parameter
// and through a nested field, and each of those callers establishes the exact
// field on the exact object it passes; the sink's method of the same name is
// reached by those very calls, and no caller of them establishes the field it
// unwraps, so it keeps the warning.
const std = @import("std");

const Region = struct {
    total: u16 = 0,
};

const Sink = struct {
    text: ?u16 = null,

    // The same name the owner's reducer carries, in a container of its own and
    // reached through a receiver of its own type.
    fn append(self: *Sink, byte: u8) void {
        self.text.? += byte;
    }
};

const Session = struct {
    region: ?Region = null,

    // Reached as `self.append(...)` from a caller that proves `region`.
    fn append(self: *Session, sink: *Sink, byte: u8) void {
        self.region.?.total += byte;
        sink.append(byte);
    }

    fn drive(self: *Session, sink: *Sink, byte: u8) void {
        if (self.region != null) {
            self.append(sink, byte);
        }
    }
};

const Owner = struct {
    session: Session = .{},

    // Reached as `self.append(...)` and as `self.session.append(...)`, from
    // callers that prove `session.region` on the object they pass.
    fn append(self: *Owner, sink: *Sink, byte: u8) void {
        self.session.region.?.total += byte;
        sink.append(byte);
    }

    fn drive(self: *Owner, sink: *Sink, byte: u8) void {
        if (self.session.region != null) {
            self.append(sink, byte);
        }
    }

    fn driveSession(self: *Owner, sink: *Sink, byte: u8) void {
        if (self.session.region != null) {
            self.session.append(sink, byte);
        }
    }
};

test "distinct receivers: every caller of the owner's reducer proves its field" {
    var sink: Sink = .{ .text = 0 };
    var owner: Owner = .{ .session = .{ .region = .{} } };

    owner.drive(&sink, 'h');
    owner.driveSession(&sink, 'i');
    owner.session.drive(&sink, '!');

    try std.testing.expectEqual(@as(u16, 242), sink.text orelse return error.MissingSinkText);
    try std.testing.expectEqual(@as(u16, 242), owner.session.region.?.total);
}

pub fn appendToUnknownSink(sink: *Sink, byte: u8) void {
    sink.append(byte);
}
