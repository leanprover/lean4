// Root module re-exporting all runtime stubs

pub const alloc = @import("alloc.zig");
pub const apply = @import("apply.zig");
pub const array = @import("array.zig");
pub const box = @import("box.zig");
pub const ctor = @import("ctor.zig");
pub const dbg = @import("dbg.zig");
pub const float = @import("float.zig");
pub const init = @import("init.zig");
pub const int = @import("int.zig");
pub const int_conv = @import("int_conv.zig");
pub const io_error = @import("io_error.zig");
pub const io_errno = @import("io_errno.zig");
pub const io_result = @import("io_result.zig");
pub const io_min = @import("io_min.zig");
pub const misc = @import("misc.zig");
pub const nat_constructors = @import("nat_constructors.zig");
pub const nat_arithmetic = @import("nat_arithmetic.zig");
pub const mpz_zig = @import("mpz_zig");
pub const mpz_object = @import("mpz_object.zig");
pub const object = @import("object.zig");
pub const once = @import("once.zig");
pub const rc = @import("rc.zig");
pub const st_ref = @import("st_ref.zig");
pub const string = @import("string.zig");
pub const sync = @import("sync.zig");
pub const task = @import("task.zig");
pub const task_manager = @import("task_manager.zig");
pub const task_manager_export = @import("task_manager_export.zig");
pub const thread = @import("thread.zig");
pub const thunk = @import("thunk.zig");
pub const uint_conv = @import("uint.zig");
pub const utf8 = @import("utf8.zig");

comptime {
    _ = alloc;
}
comptime {
    _ = apply;
}
comptime {
    _ = array;
}
comptime {
    _ = box;
}
comptime {
    _ = ctor;
}
comptime {
    _ = dbg;
}
comptime {
    _ = float;
}
comptime {
    _ = init;
}
comptime {
    _ = int;
}
comptime {
    _ = int_conv;
}
comptime {
    _ = io_error;
}
comptime {
    _ = io_errno;
}
comptime {
    _ = io_result;
}
comptime {
    _ = io_min;
}
comptime {
    _ = misc;
}
comptime {
    _ = nat_constructors;
}
comptime {
    _ = nat_arithmetic;
}
comptime {
    _ = mpz_zig;
}
comptime {
    _ = mpz_object;
}
comptime {
    _ = object;
}
comptime {
    _ = once;
}
comptime {
    _ = rc;
}
comptime {
    _ = st_ref;
}
comptime {
    _ = string;
}
comptime {
    _ = sync;
}
comptime {
    _ = task;
}
comptime {
    _ = task_manager;
}
comptime {
    _ = task_manager_export;
}
comptime {
    _ = thread;
}
comptime {
    _ = thunk;
}
comptime {
    _ = uint_conv;
}
comptime {
    _ = utf8;
}
