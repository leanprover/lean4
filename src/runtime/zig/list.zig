// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const lean = @import("lean_object.zig");
const object = @import("object.zig");
const runtime_options = @import("runtime_options");

// Mangled name emitted by the Lean compiler for List.lengthTR's reducer argument.
fn l_List_lengthTR___redArg(list: *anyopaque) callconv(.c) *anyopaque {
    var len: usize = 0;
    var current: ?*anyopaque = list;
    while (current) |node| {
        const tag = object.lean_obj_tag(node);
        if (tag == 0) {
            break;
        } else if (tag == 1) {
            len += 1;
            const ctor: *lean.lean_ctor_object = @ptrCast(@alignCast(node));
            const slots: [*]?*anyopaque = @ptrCast(&ctor.m_objs);
            current = slots[1];
        } else {
            @panic("l_List_lengthTR___redArg: invalid list constructor tag");
        }
    }
    return object.lean_box(len).?;
}

comptime {
    if (runtime_options.export_lean_helpers) {
        @export(&l_List_lengthTR___redArg, .{ .name = "l_List_lengthTR___redArg" });
    }
}
