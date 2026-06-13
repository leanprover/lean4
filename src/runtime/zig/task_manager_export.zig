const CTaskManager = opaque {};

pub export var g_task_manager: ?*CTaskManager = null;

pub fn set(manager: ?*anyopaque) void {
    g_task_manager = if (manager) |ptr| @ptrCast(ptr) else null;
}

pub fn get() ?*CTaskManager {
    return g_task_manager;
}
