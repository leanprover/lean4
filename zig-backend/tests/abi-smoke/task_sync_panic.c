#include <assert.h>
#include <sched.h>
#include <signal.h>
#include <stdatomic.h>
#include <unistd.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);

static atomic_bool g_release_outer = false;
static atomic_bool g_release_inner = false;

static void spin_until_true(atomic_bool * flag) {
    while (!atomic_load_explicit(flag, memory_order_acquire)) {
        sched_yield();
    }
}

static lean_object * blocked_outer(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_outer);
    return lean_box(1);
}

static lean_object * blocked_inner(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_inner);
    return lean_box(2);
}

static lean_object * sync_get_inner(lean_object * inner_task, lean_object * value) {
    assert(lean_unbox(value) == 1);
    (void)lean_task_get(inner_task);
    return lean_task_pure(lean_box(0));
}

int main(void) {
    alarm(5);
    assert(leanrt_test_runtime_task_manager_init(1));
    atomic_store_explicit(&g_release_outer, false, memory_order_release);
    atomic_store_explicit(&g_release_inner, false, memory_order_release);

    lean_object * outer_closure = lean_alloc_closure((void *)blocked_outer, 1, 0);
    lean_object * outer_task = lean_task_spawn_core(outer_closure, 0, 0);

    lean_object * inner_closure = lean_alloc_closure((void *)blocked_inner, 1, 0);
    lean_object * inner_task = lean_task_spawn_core(inner_closure, 0, 0);

    lean_inc(inner_task);
    lean_object * bind_closure = lean_alloc_closure((void *)sync_get_inner, 2, 1);
    lean_closure_set(bind_closure, 0, inner_task);
    lean_object * sync_task = lean_task_bind_core(outer_task, bind_closure, 0, 1, 0);
    (void)sync_task;

    atomic_store_explicit(&g_release_outer, true, memory_order_release);
    (void)leanrt_test_runtime_task_wait(outer_task);

    lean_dec(outer_task);
    lean_dec(inner_task);
    leanrt_test_runtime_task_manager_finalize();
    alarm(0);
    return 0;
}
