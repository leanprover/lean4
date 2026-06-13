#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <lean/lean.h>

#define LOW_COUNT 100u
#define HIGH_COUNT 100u
#define TOTAL_COUNT (LOW_COUNT + HIGH_COUNT)

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

static _Atomic unsigned g_order_index = 0;
static unsigned g_order[TOTAL_COUNT];

static lean_object * fairness_task(lean_object * payload) {
    unsigned token = (unsigned)lean_unbox(payload);
    unsigned slot = atomic_fetch_add_explicit(&g_order_index, 1, memory_order_acq_rel);
    assert(slot < TOTAL_COUNT);
    g_order[slot] = token;
    return payload;
}

static unsigned token_prio(unsigned token) {
    return token >> 16;
}

static unsigned token_id(unsigned token) {
    return token & 0xffffu;
}

static unsigned make_token(unsigned prio, unsigned id) {
    return (prio << 16) | id;
}

static void spawn_tasks(lean_object ** tasks, unsigned prio, unsigned count, unsigned offset) {
    for (unsigned i = 0; i < count; ++i) {
        lean_object * closure = lean_alloc_closure((void *)fairness_task, 2, 1);
        lean_closure_set(closure, 0, lean_box(make_token(prio, i)));
        tasks[offset + i] = lean_task_spawn_core(closure, prio, false);
    }
}

static void await_tasks(lean_object ** tasks, unsigned count) {
    for (unsigned i = 0; i < count; ++i) {
        lean_object * result = lean_task_get(tasks[i]);
        assert(result != NULL);
        lean_dec(tasks[i]);
    }
}

int main(void) {
    lean_object * tasks[TOTAL_COUNT];

    memset(g_order, 0, sizeof(g_order));
    atomic_store_explicit(&g_order_index, 0, memory_order_release);

    lean_initialize_runtime_module();
    lean_initialize_thread();
    lean_init_task_manager_using(1);

    spawn_tasks(tasks, 1, HIGH_COUNT, 0);
    spawn_tasks(tasks, 0, LOW_COUNT, HIGH_COUNT);
    await_tasks(tasks, TOTAL_COUNT);

    lean_finalize_task_manager();
    lean_finalize_thread();

    assert(atomic_load_explicit(&g_order_index, memory_order_acquire) == TOTAL_COUNT);
    for (unsigned i = 0; i < HIGH_COUNT; ++i) {
        assert(token_prio(g_order[i]) == 1);
        assert(token_id(g_order[i]) == i);
    }
    for (unsigned i = 0; i < LOW_COUNT; ++i) {
        assert(token_prio(g_order[HIGH_COUNT + i]) == 0);
        assert(token_id(g_order[HIGH_COUNT + i]) == i);
    }

    printf("fairness: high_before_low=%u fifo=1\n", HIGH_COUNT);
    return 0;
}
