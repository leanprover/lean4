#include "runtime/object.h"

extern "C" lean_task_object *lean_zig_current_task_get();
extern "C" lean_task_object *leanrt_cpp_partial_hidden_current_task_get();

static lean_object * check_current_task_tls(lean_object * unit) {
    (void)unit;
    return lean::box(leanrt_cpp_partial_hidden_current_task_get() == lean_zig_current_task_get());
}

extern "C" int leanrt_test_current_task_tls_smoke(void) {
    lean_init_task_manager_using(1);

    lean_object * closure = lean_alloc_closure(reinterpret_cast<void *>(check_current_task_tls), 1, 0);
    lean_object * task = lean_task_spawn_core(closure, 0, false);
    bool ok = lean_unbox(lean_task_get(task)) == 1;

    lean_dec(task);
    lean_finalize_task_manager();
    return ok;
}
