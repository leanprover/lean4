/*
Release the roots of random heaps one at a time through `lean_dec_ref`, and print each heap, the
objects each release reclaims and the counts it leaves, for `Replay.lean` to compare with `drain`.

Nodes are constructors, arrays, closures and thunks with single-threaded, thread-shared, persistent
and sticky counts. Their slots hold other nodes, scalars and, in thunks, `NULL`, including cycles,
self-loops and repeated pointers. Each node's last slot holds a marker whose finalizer reports that
the node was reclaimed. Only the slots that hold nodes are printed: they are the fields of the
ownership graph, while scalars, `NULL` and the markers own no reference to a node.
*/
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);
void exit(int status);

void lean_initialize_runtime_module(void);

#define CHECK(c) do { \
    if (!(c)) { \
        printf("%s:%d: check failed: %s (case %u)\n", __FILE__, __LINE__, #c, seed); \
        exit(1); \
    } \
} while (0)

enum { N = 12, F = 5, CASES = 1500 };
enum { CTOR, ARRAY, CLOSURE, THUNK };

static unsigned seed;
static uint32_t rng;
static uint32_t random32(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

static lean_external_class * marker_class;
static unsigned finalized[N];
static bool live[N];

static void finalize(void * data) {
    unsigned id = (unsigned)(uintptr_t)data;
    CHECK(id < N && finalized[id]++ == 0);
    if (live[id]) {
        live[id] = false;
        printf(" %u", id);
    }
}
static void foreach(void * data, b_lean_obj_arg fn) { (void)data; (void)fn; }

static unsigned n, kind[N], degree[N];
static lean_object * nodes[N];
static int edges[N][F]; // a node, or -1 for a scalar or `NULL`

static lean_object ** slots(unsigned i) {
    switch (kind[i]) {
    case CTOR: return lean_ctor_obj_cptr(nodes[i]);
    case ARRAY: return lean_array_cptr(nodes[i]);
    default: return lean_closure_arg_cptr(nodes[i]);
    }
}

static void heap_case(void) {
    rng = seed * 2654435761u;
    n = 1 + random32() % N;
    unsigned roots = n + random32() % (n + 1), root[2 * N];
    int counts[N];
    for (unsigned i = 0; i < n; ++i) {
        root[i] = i;
        counts[i] = 1;
        finalized[i] = 0;
        live[i] = true;
    }
    for (unsigned r = n; r < roots; ++r) ++counts[root[r] = random32() % n];
    for (unsigned i = 0; i < n; ++i) {
        kind[i] = random32() % 4;
        degree[i] = kind[i] == THUNK ? 1 : random32() % (F + 1);
        for (unsigned f = 0; f < degree[i]; ++f) {
            /* Alternate acyclic and arbitrary graphs. */
            unsigned target = random32() % (n + 2);
            if ((seed & 1) && target <= i) target = n;
            edges[i][f] = target < n ? (int)target : -1;
            if (target < n) ++counts[target];
        }
        lean_object * m = lean_alloc_external(marker_class, (void *)(uintptr_t)i);
        unsigned k = degree[i];
        switch (kind[i]) {
        case CTOR: nodes[i] = lean_alloc_ctor(i % 8, k + 1, 0); break;
        case ARRAY: nodes[i] = lean_alloc_array(k + 1, k + 3); break;
        case CLOSURE: nodes[i] = lean_alloc_closure(NULL, k + 2, k + 1); break;
        default: nodes[i] = lean_mk_thunk(NULL); lean_to_thunk(nodes[i])->m_value = m; break;
        }
        if (kind[i] != THUNK) slots(i)[k] = m;
    }
    for (unsigned i = 0; i < n; ++i) {
        for (unsigned f = 0; f < degree[i]; ++f) {
            int e = edges[i][f];
            if (kind[i] == THUNK) lean_to_thunk(nodes[i])->m_closure = e < 0 ? NULL : nodes[e];
            else slots(i)[f] = e < 0 ? lean_box(f) : nodes[e];
        }
        unsigned mode = random32() % 16;
        if (mode < 7) counts[i] = -counts[i];
        else if (seed % 3 == 0 && mode == 7) counts[i] = 0;
        else if (seed % 3 == 0 && mode == 8) counts[i] = LEAN_RC_STICKY_DROP;
        else if (seed % 3 == 0 && mode == 9) counts[i] = LEAN_RC_STICKY;
        else if (seed % 3 == 0 && mode == 10) counts[i] = LEAN_RC_STUCK_ST;
        lean_internal_set_rc(nodes[i], counts[i]);
    }
    for (unsigned r = roots - 1; r > 0; --r) {
        unsigned j = random32() % (r + 1), t = root[r];
        root[r] = root[j];
        root[j] = t;
    }

    printf("heap");
    for (unsigned r = 0; r < roots; ++r) printf(" %u", root[r]);
    printf("\n");
    for (unsigned i = 0; i < n; ++i) {
        printf("node %d", counts[i]);
        for (unsigned f = 0; f < degree[i]; ++f)
            if (edges[i][f] >= 0) printf(" %d", edges[i][f]);
        printf("\n");
    }
    for (unsigned r = 0; r < roots; ++r) {
        CHECK(live[root[r]]);
        printf("free");
        lean_dec(nodes[root[r]]);
        printf(" rc");
        for (unsigned i = 0; i < n; ++i)
            if (live[i]) printf(" %d", lean_internal_get_rc(nodes[i]));
            else printf(" f");
        printf("\n");
    }

    /* Free what the releases keep: cycles and never-freed counts, and what those retain. */
    for (unsigned i = 0; i < n; ++i)
        if (live[i]) {
            if (kind[i] == THUNK) lean_to_thunk(nodes[i])->m_closure = NULL;
            else for (unsigned f = 0; f < degree[i]; ++f) slots(i)[f] = lean_box(0);
        }
    for (unsigned i = 0; i < n; ++i)
        if (live[i]) {
            live[i] = false;
            lean_internal_set_rc(nodes[i], 1);
            lean_dec(nodes[i]);
        }
    for (unsigned i = 0; i < n; ++i) CHECK(finalized[i] == 1);
}

int main(void) {
    lean_initialize_runtime_module();
    marker_class = lean_register_external_class(finalize, foreach);
    for (seed = 1; seed <= CASES; ++seed) heap_case();
    return 0;
}
