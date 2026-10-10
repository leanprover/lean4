/*
Compare native deletion with an independent counted-edge/LIFO interpreter.
Random graph nodes own a final marker field that exposes their visitation order.
Unary fixtures observe terminal finalizers, not the frees of unary parents.
Run this same test against the incumbent and generated collectors.
*/
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>

void lean_initialize_runtime_module(void);

#define CHECK(c) do { \
    if (!(c)) { fprintf(stderr, "%s:%d: %s (seed %u)\n", __FILE__, __LINE__, #c, seed); abort(); } \
} while (0)

enum { N = 24, F = 8, R = 2 * N, TRACE = 1024 };
static unsigned seed;
static uint32_t rng;
static unsigned actual[TRACE], expected[TRACE], finalized[TRACE];
static unsigned actual_n, expected_n;
static bool record = true;
static uint64_t digest = 1469598103934665603ULL;
static lean_external_class * marker_class;
static lean_object * reentrant;

static void finalize(void * data) {
    unsigned id = (unsigned)(uintptr_t)data;
    CHECK(id < TRACE && ++finalized[id] == 1);
    if (record) {
        CHECK(actual_n < TRACE);
        actual[actual_n++] = id;
        digest = (digest ^ id) * 1099511628211ULL;
    }
    if (id == 900 && reentrant) {
        CHECK(finalized[901] == 0 && finalized[902] == 0);
        lean_object * nested = reentrant;
        reentrant = NULL;
        lean_dec(nested);
        CHECK(finalized[901] == 1 && finalized[902] == 0);
    }
}

static void foreach(void * data, b_lean_obj_arg fn) { (void)data; (void)fn; }
static lean_object * marker(unsigned id) {
    return lean_alloc_external(marker_class, (void *)(uintptr_t)id);
}
static lean_object * box(lean_object * child) {
    lean_object * o = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(o, 0, child);
    return o;
}
static void reset(void) {
    actual_n = expected_n = 0;
    for (unsigned i = 0; i < TRACE; ++i) finalized[i] = 0;
}
static void compare_trace(void) {
    CHECK(actual_n == expected_n);
    for (unsigned i = 0; i < actual_n; ++i) CHECK(actual[i] == expected[i]);
}

static lean_object * nodes[N];
static int edges[N][F], counts[N];
static unsigned degree[N], kind[N], stack[N], top;
static bool live[N];

#include "counted_edge_model.h"

static lean_object ** fields(unsigned i) {
    switch (kind[i]) {
    case 0: return lean_ctor_obj_cptr(nodes[i]);
    case 1: return lean_array_cptr(nodes[i]);
    default: return lean_closure_arg_cptr(nodes[i]);
    }
}

static void graph_case(void) {
    reset();
    rng = seed;
    top = 0;
    unsigned roots[R];
    for (unsigned i = 0; i < N; ++i) {
        counts[i] = 1;
        roots[i] = i;
        live[i] = true;
    }
    for (unsigned i = N; i < R; ++i) ++counts[roots[i] = random32() % N];
    for (unsigned i = 0; i < N; ++i) {
        degree[i] = random32() % (F + 1);
        kind[i] = random32() % 3;
        for (unsigned f = 0; f < degree[i]; ++f) {
            /* Alternate DAGs and arbitrary graphs, including self-loops and repeated fields. */
            unsigned target = random32() % (N + 4);
            if ((seed & 1) && target <= i) target = N;
            edges[i][f] = target < N ? (int)target : -1;
            if (target < N) ++counts[target];
        }
        unsigned n = degree[i] + 1;
        switch (kind[i]) {
        case 0: nodes[i] = lean_alloc_ctor(i % (LeanMaxCtorTag + 1), n, 0); break;
        case 1: nodes[i] = lean_alloc_array(n, n + 3); break;
        default: nodes[i] = lean_alloc_closure(NULL, n + 1, n); break;
        }
    }
    for (unsigned i = 0; i < N; ++i) {
        lean_object ** p = fields(i);
        for (unsigned f = 0; f < degree[i]; ++f)
            p[f] = edges[i][f] < 0 ? lean_box(f) : nodes[edges[i][f]];
        p[degree[i]] = marker(i);
        unsigned mode = random32() % 16;
        if (mode < 7) counts[i] = -counts[i];
        else if (mode == 7 && seed % 3 == 0) counts[i] = 0;
        else if (mode == 8 && seed % 3 == 0) counts[i] = LEAN_RC_STICKY_DROP;
        else if (mode == 9 && seed % 3 == 0) counts[i] = LEAN_RC_STUCK_ST;
        lean_internal_set_rc(nodes[i], counts[i]);
    }
    for (unsigned i = R - 1; i > 0; --i) {
        unsigned j = random32() % (i + 1), tmp = roots[i];
        roots[i] = roots[j];
        roots[j] = tmp;
    }
    for (unsigned r = 0; r < R; ++r) {
        model_drop(roots[r], TRACE);
        lean_dec(nodes[roots[r]]);
        compare_trace();
        for (unsigned i = 0; i < N; ++i)
            if (live[i]) CHECK(lean_internal_get_rc(nodes[i]) == counts[i]);
    }
    /* Break deliberately retained cycles/sticky subgraphs before freeing the test fixture. */
    record = false;
    for (unsigned i = 0; i < N; ++i)
        if (live[i])
            for (unsigned f = 0; f < degree[i]; ++f) fields(i)[f] = lean_box(0);
    for (unsigned i = 0; i < N; ++i)
        if (live[i]) {
            lean_internal_set_rc(nodes[i], 1);
            lean_dec(nodes[i]);
        }
    record = true;
    for (unsigned i = 0; i < N; ++i) CHECK(finalized[i] == 1);
}

static void unary_pending_reentry(bool shared) {
    enum { DEPTH = 4 };
    reset();
    CHECK(reentrant == NULL);
    /* The callback owns this independent root; it never borrows a dying parent. */
    reentrant = box(box(marker(901)));
    lean_object * terminal = marker(900);
    lean_object * chain = terminal;
    for (unsigned i = 0; i < DEPTH; ++i) chain = box(chain);
    lean_object * older = marker(902);
    lean_object * outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, older);
    lean_ctor_set(outer, 1, chain);
    if (shared) {
        lean_mark_mt(outer);
        lean_mark_mt(reentrant);
    }
    int rc = shared ? -1 : 1;
    CHECK(lean_internal_get_rc(outer) == rc);
    CHECK(lean_internal_get_rc(older) == rc);
    CHECK(lean_internal_get_rc(reentrant) == rc);
    lean_object * cursor = chain;
    for (unsigned i = 0; i < DEPTH; ++i) {
        CHECK(lean_ctor_num_objs(cursor) == 1);
        CHECK(lean_internal_get_rc(cursor) == rc);
        cursor = lean_ctor_get(cursor, 0);
    }
    CHECK(cursor == terminal && lean_internal_get_rc(terminal) == rc);
    /* LIFO leaves older pending through the direct chain and nested deletion. */
    lean_dec(outer);
    CHECK(reentrant == NULL);
    expected[expected_n++] = 900;
    expected[expected_n++] = 901;
    expected[expected_n++] = 902;
    compare_trace();
}

static void special_objects(void) {
    reset();
    lean_object * t = lean_mk_thunk(marker(0));
    lean_to_thunk(t)->m_value = marker(1);
    lean_dec(t);
    expected[expected_n++] = 1;
    expected[expected_n++] = 0;
    compare_trace();

    lean_dec(lean_thunk_pure(marker(2)));
    lean_dec(lean_mk_thunk(marker(3)));
    lean_dec(lean_st_mk_ref(marker(4)));
    lean_dec(lean_st_mk_ref(NULL));
    lean_dec(lean_task_pure(marker(5)));
    for (unsigned i = 2; i <= 5; ++i) expected[expected_n++] = i;
    compare_trace();

    /* Empty, scalar-only, and variable-capacity allocations exercise each native destructor. */
    lean_dec(lean_alloc_ctor(0, 0, 0));
    lean_dec(lean_alloc_array(0, 9));
    lean_dec(lean_alloc_closure(NULL, 1, 0));
    lean_dec(lean_alloc_sarray(1, 7, 15));
    lean_dec(lean_alloc_sarray(8, 3, 8));
    lean_dec(lean_mk_string("collector"));
    lean_dec(lean_uint64_to_nat(UINT64_MAX));

    reset();
    reentrant = box(marker(901));
    lean_object * outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, marker(902));
    lean_ctor_set(outer, 1, marker(900));
    lean_dec(outer);
    expected[expected_n++] = 900;
    expected[expected_n++] = 901;
    expected[expected_n++] = 902;
    compare_trace();

    reset();
    lean_object * chain = marker(0);
    for (unsigned i = 0; i < 100000; ++i) chain = box(chain);
    lean_dec(chain);
    expected[expected_n++] = 0;
    compare_trace();
}

int main(void) {
    lean_initialize_runtime_module();
    marker_class = lean_register_external_class(finalize, foreach);
    for (seed = 1; seed <= 4096; ++seed) graph_case();
    special_objects();
    unary_pending_reentry(false);
    unary_pending_reentry(true);
    printf("4096 graph cases; ST/MT unary pending/reentry cases; deletion trace %llx\n",
        (unsigned long long)digest);
    return 0;
}
