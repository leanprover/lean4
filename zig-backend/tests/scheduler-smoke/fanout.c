#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

#include <lean/lean.h>

#define FANOUT_COUNT 1000u
#define DEP_COUNT 3u
#define SYNC_COUNT 4u
#define LEAN_SYNC_PRIO UINT_MAX

#ifdef SCHEDULER_REFERENCE_CPP
extern void leanrt_cpp_partial_hidden_lean_init_task_manager_impl(void);
extern void leanrt_cpp_partial_hidden_lean_init_task_manager_using_impl(unsigned num_workers);
extern void leanrt_cpp_partial_hidden_lean_finalize_task_manager_impl(void);
extern lean_object *leanrt_cpp_partial_hidden_lean_task_spawn_core_impl(lean_object *c, unsigned prio, bool keep_alive);
extern lean_object *leanrt_cpp_partial_hidden_lean_task_pure_impl(lean_object *a);
extern lean_object *leanrt_cpp_partial_hidden_lean_task_bind_core_impl(lean_object *x, lean_object *f, unsigned prio, bool sync, bool keep_alive);
extern lean_object *leanrt_cpp_partial_hidden_lean_task_get_impl(lean_object *t);

#define lean_init_task_manager leanrt_cpp_partial_hidden_lean_init_task_manager_impl
#define lean_init_task_manager_using leanrt_cpp_partial_hidden_lean_init_task_manager_using_impl
#define lean_finalize_task_manager leanrt_cpp_partial_hidden_lean_finalize_task_manager_impl
#define lean_task_spawn_core leanrt_cpp_partial_hidden_lean_task_spawn_core_impl
#define lean_task_pure leanrt_cpp_partial_hidden_lean_task_pure_impl
#define lean_task_bind_core leanrt_cpp_partial_hidden_lean_task_bind_core_impl
#define lean_task_get leanrt_cpp_partial_hidden_lean_task_get_impl
#endif

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);

struct scheduler_snapshot {
    uint64_t seed;
    uint64_t rc_total;
    uint64_t dep_shape_hash;
    unsigned sync_prio_order[SYNC_COUNT];
    size_t tagged_alloc_alloc;
    size_t tagged_alloc_free;
    ptrdiff_t tagged_alloc_balance;
};

static _Atomic unsigned g_sync_index = 0;
static unsigned g_sync_order[SYNC_COUNT];
static _Atomic unsigned g_dep_release = 0;

static uint64_t fnv1a_mix(uint64_t hash, uint64_t word) {
    unsigned shift;
    for (shift = 0; shift < 64; shift += 8) {
        hash ^= (word >> shift) & 0xffu;
        hash *= UINT64_C(1099511628211);
    }
    return hash;
}

static uint64_t parse_seed(void) {
    char const * raw = getenv("SCHEDULER_SMOKE_SEED");
    char * end = NULL;
    unsigned long long value;
    if (raw == NULL || *raw == '\0') {
        return UINT64_C(0xC0FFEE);
    }
    value = strtoull(raw, &end, 0);
    if (end == raw || *end != '\0') {
        return UINT64_C(0xC0FFEE);
    }
    return (uint64_t)value;
}

static uint64_t next_state(uint64_t * state) {
    *state = (*state * UINT64_C(6364136223846793005)) + UINT64_C(1442695040888963407);
    return *state;
}

static lean_object * fanout_task(lean_object * payload) {
    return payload;
}

static lean_object * root_task(lean_object * unit) {
    (void)unit;
    while (atomic_load_explicit(&g_dep_release, memory_order_acquire) == 0) {
        sched_yield();
    }
    return lean_box(9);
}

static lean_object * dep_task_a(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(11));
}

static lean_object * dep_task_b(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(12));
}

static lean_object * dep_task_c(lean_object * value) {
    assert(lean_unbox(value) == 9);
    return lean_task_pure(lean_box(13));
}

static lean_object * sync_task(lean_object * payload) {
    unsigned slot = atomic_fetch_add_explicit(&g_sync_index, 1, memory_order_acq_rel);
    unsigned value = (unsigned)lean_unbox(payload);
    assert(slot < SYNC_COUNT);
    g_sync_order[slot] = value;
    return payload;
}

static uint64_t run_fanout_workload(uint64_t seed) {
    lean_object * tasks[FANOUT_COUNT];
    uint64_t rc_total = 0;
    uint64_t state = seed;
    unsigned i;

    for (i = 0; i < FANOUT_COUNT; ++i) {
        unsigned prio = (unsigned)(next_state(&state) % 3u);
        unsigned value = (unsigned)(next_state(&state) & 0xffffu);
        lean_object * closure = lean_alloc_closure((void *)fanout_task, 2, 1);
        lean_closure_set(closure, 0, lean_box(value));
        tasks[i] = lean_task_spawn_core(closure, prio, false);
    }

    for (i = 0; i < FANOUT_COUNT; ++i) {
        lean_object * result = lean_task_get(tasks[i]);
        rc_total += (uint64_t)lean_unbox(result);
        lean_dec(tasks[i]);
    }

    return rc_total;
}

static uint64_t run_dep_shape_workload(void) {
    uint64_t hash = UINT64_C(1469598103934665603);
    lean_object * root_closure;
    lean_object * root_task_obj;
    lean_object * dep_a;
    lean_object * dep_b;
    lean_object * dep_c;
    lean_task_object * dep_it;

    atomic_store_explicit(&g_dep_release, 0, memory_order_release);
    root_closure = lean_alloc_closure((void *)root_task, 1, 0);
    root_task_obj = lean_task_spawn_core(root_closure, 0, false);

    lean_inc(root_task_obj);
    dep_a = lean_task_bind_core(root_task_obj, lean_alloc_closure((void *)dep_task_a, 1, 0), 0, false, false);
    lean_inc(root_task_obj);
    dep_b = lean_task_bind_core(root_task_obj, lean_alloc_closure((void *)dep_task_b, 1, 0), 0, false, false);
    lean_inc(root_task_obj);
    dep_c = lean_task_bind_core(root_task_obj, lean_alloc_closure((void *)dep_task_c, 1, 0), 0, false, false);

    dep_it = lean_to_task(root_task_obj)->m_imp->m_head_dep;
    while (dep_it != NULL) {
        if (dep_it == lean_to_task(dep_a)) {
            hash = fnv1a_mix(hash, 11);
        } else if (dep_it == lean_to_task(dep_b)) {
            hash = fnv1a_mix(hash, 12);
        } else if (dep_it == lean_to_task(dep_c)) {
            hash = fnv1a_mix(hash, 13);
        } else {
            assert(0 && "unexpected dependency node");
        }
        dep_it = dep_it->m_imp->m_next_dep;
    }

    atomic_store_explicit(&g_dep_release, 1, memory_order_release);
    assert(lean_unbox(lean_task_get(dep_a)) == 11);
    assert(lean_unbox(lean_task_get(dep_b)) == 12);
    assert(lean_unbox(lean_task_get(dep_c)) == 13);

    lean_dec(root_task_obj);
    lean_dec(dep_a);
    lean_dec(dep_b);
    lean_dec(dep_c);
    return hash;
}

static void run_sync_workload(void) {
    unsigned i;
    atomic_store_explicit(&g_sync_index, 0, memory_order_release);
    memset(g_sync_order, 0, sizeof(g_sync_order));

    for (i = 0; i < SYNC_COUNT; ++i) {
        lean_object * closure = lean_alloc_closure((void *)sync_task, 2, 1);
        lean_object * task;
        lean_closure_set(closure, 0, lean_box(i));
        task = lean_task_spawn_core(closure, LEAN_SYNC_PRIO, false);
        assert(lean_unbox(lean_task_get(task)) == i);
        lean_dec(task);
    }
}

static void emit_json(FILE * out, struct scheduler_snapshot const * snapshot) {
    unsigned i;
    fprintf(out, "{\n");
    fprintf(out, "  \"seed\": %" PRIu64 ",\n", snapshot->seed);
    fprintf(out, "  \"rc_total\": %" PRIu64 ",\n", snapshot->rc_total);
    fprintf(out, "  \"dep_shape_hash\": %" PRIu64 ",\n", snapshot->dep_shape_hash);
    fprintf(out, "  \"sync_prio_order\": [");
    for (i = 0; i < SYNC_COUNT; ++i) {
        fprintf(out, "%s%u", i == 0 ? "" : ", ", snapshot->sync_prio_order[i]);
    }
    fprintf(out, "],\n");
    fprintf(out, "  \"tagged_alloc_balance\": {\n");
    fprintf(out, "    \"alloc\": %zu,\n", snapshot->tagged_alloc_alloc);
    fprintf(out, "    \"free\": %zu,\n", snapshot->tagged_alloc_free);
    fprintf(out, "    \"net\": %td\n", snapshot->tagged_alloc_balance);
    fprintf(out, "  }\n");
    fprintf(out, "}\n");
}

int main(int argc, char ** argv) {
    struct scheduler_snapshot snapshot;
    char const * json_path = NULL;
    FILE * out = stdout;

    if (argc == 3 && strcmp(argv[1], "--emit-json") == 0) {
        json_path = argv[2];
    } else if (argc != 1) {
        fprintf(stderr, "usage: %s [--emit-json path]\n", argv[0]);
        return 2;
    }

    lean_initialize_runtime_module();
    lean_initialize_thread();

    snapshot.seed = parse_seed();
    lean_init_task_manager_using(4);
#ifndef SCHEDULER_REFERENCE_CPP
    leanrt_test_allocator_reset_counters();
#endif
    snapshot.rc_total = run_fanout_workload(snapshot.seed);
#ifdef SCHEDULER_REFERENCE_CPP
    snapshot.tagged_alloc_alloc = 0;
    snapshot.tagged_alloc_free = 0;
    snapshot.tagged_alloc_balance = 0;
#else
    snapshot.tagged_alloc_alloc = leanrt_test_allocator_alloc_count();
    snapshot.tagged_alloc_free = leanrt_test_allocator_free_count();
    snapshot.tagged_alloc_balance =
        (ptrdiff_t)snapshot.tagged_alloc_alloc - (ptrdiff_t)snapshot.tagged_alloc_free;
#endif
    lean_finalize_task_manager();

    lean_init_task_manager_using(1);
    snapshot.dep_shape_hash = run_dep_shape_workload();
    run_sync_workload();
    lean_finalize_task_manager();

    memcpy(snapshot.sync_prio_order, g_sync_order, sizeof(g_sync_order));
    lean_finalize_thread();

    if (json_path != NULL) {
        out = fopen(json_path, "w");
        if (out == NULL) {
            perror("fopen");
            return 1;
        }
    }

    emit_json(out, &snapshot);

    if (json_path != NULL) {
        fclose(out);
    }
    return 0;
}
