#include <assert.h>
#include <signal.h>
#include <unistd.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);

static lean_object * nested_get(lean_object * depth, lean_object * unit) {
    (void)unit;
    size_t remaining = lean_unbox(depth);
    if (remaining == 0) {
        return lean_box(0);
    }

    lean_object * closure = lean_alloc_closure((void *)nested_get, 2, 1);
    lean_closure_set(closure, 0, lean_box(remaining - 1));
    lean_object * child = lean_task_spawn_core(closure, 0, 0);
    size_t value = lean_unbox(lean_task_get(child));
    lean_dec(child);
    return lean_box(value + 1);
}

int main(void) {
    alarm(5);
    assert(leanrt_test_runtime_task_manager_init(1));

    lean_object * closure = lean_alloc_closure((void *)nested_get, 2, 1);
    lean_closure_set(closure, 0, lean_box(100));
    lean_object * task = lean_task_spawn_core(closure, 0, 0);

    assert(lean_unbox(lean_task_get(task)) == 100);

    lean_dec(task);
    leanrt_test_runtime_task_manager_finalize();
    alarm(0);
    return 0;
}
