const lean = @import("lean_object.zig");

threadlocal var g_current_task_object: ?*lean.lean_task_object = null;

pub fn get() ?*lean.lean_task_object {
    return g_current_task_object;
}

pub fn swap(task: ?*lean.lean_task_object) ?*lean.lean_task_object {
    const prev = g_current_task_object;
    g_current_task_object = task;
    return prev;
}

pub export fn lean_zig_current_task_get() callconv(.c) ?*lean.lean_task_object {
    return get();
}

pub export fn lean_zig_current_task_swap(task: ?*lean.lean_task_object) callconv(.c) ?*lean.lean_task_object {
    return swap(task);
}
