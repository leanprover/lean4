#include <assert.h>
#include <sched.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);
/* Verifies intrusive dep-list ordering and linkage. */

static atomic_bool g_release_root = false;

static void spin_until_true(atomic_bool * flag) {
    while (!atomic_load_explicit(flag, memory_order_acquire)) {
        sched_yield();
    }
}

static lean_object * blocked_root(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_root);
    return lean_box(9);
}

static lean_object * return_eleven(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(11));
}

static lean_object * return_twelve(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(12));
}

static lean_object * return_thirteen(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(13));
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));
    atomic_store_explicit(&g_release_root, false, memory_order_release);

    lean_object * root_closure = lean_alloc_closure((void *)blocked_root, 1, 0);
    lean_object * root_task = lean_task_spawn_core(root_closure, 0, 0);

    lean_inc(root_task);
    lean_object * bind_b = lean_alloc_closure((void *)return_eleven, 1, 0);
    lean_object * task_b = lean_task_bind_core(root_task, bind_b, 0, 0, 0);

    lean_inc(root_task);
    lean_object * bind_c = lean_alloc_closure((void *)return_twelve, 1, 0);
    lean_object * task_c = lean_task_bind_core(root_task, bind_c, 0, 0, 0);

    lean_inc(root_task);
    lean_object * bind_d = lean_alloc_closure((void *)return_thirteen, 1, 0);
    lean_object * task_d = lean_task_bind_core(root_task, bind_d, 0, 0, 0);

    lean_task_object * root = lean_to_task(root_task);
    assert(root->m_imp != NULL);
    assert(root->m_imp->m_head_dep == lean_to_task(task_d));
    assert(root->m_imp->m_head_dep->m_imp->m_next_dep == lean_to_task(task_c));
    assert(root->m_imp->m_head_dep->m_imp->m_next_dep->m_imp->m_next_dep == lean_to_task(task_b));
    assert(root->m_imp->m_head_dep->m_imp->m_next_dep->m_imp->m_next_dep->m_imp->m_next_dep == NULL);

    atomic_store_explicit(&g_release_root, true, memory_order_release);
    assert(leanrt_test_runtime_task_wait(task_b));
    assert(leanrt_test_runtime_task_wait(task_c));
    assert(leanrt_test_runtime_task_wait(task_d));

    lean_dec(root_task);
    lean_dec(task_b);
    lean_dec(task_c);
    lean_dec(task_d);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
