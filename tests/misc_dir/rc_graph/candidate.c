/*
Execute the generated entry point over a checked heap, independently of lean_dec_ref_cold.
Per-kind primitives check layouts, accesses after disposal, and destructor order. A separate
counted-edge interpreter checks counters, pending work, and the exact disposal trace.
Scheduled counter changes check decisions across the shared read/guard/update boundary.
*/
#include <lean/lean.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>

#define CHECK(c) do { \
    if (!(c)) { fprintf(stderr, "%s:%d: %s (seed %u)\n", __FILE__, __LINE__, #c, seed); exit(1); } \
} while (0)

enum { N = 24, F = 8, R = 2 * N };
typedef struct {
    uint32_t rc;
    size_t next;
    size_t fields[F];
    size_t count;
    size_t fields_read;
    uint8_t tag;
    bool disposed;
    bool count_read;
    bool begin_read;
    bool closure_read;
    bool value_read;
    bool mpz_destroyed;
    bool finalized;
} Node;

static Node nodes[N];
static unsigned seed, actual[N], expected[N], actual_n, expected_n;
static int edges[N][F], counts[N];
static unsigned degree[N], stack[N], top;
static bool live[N];
static uint32_t rng;
static uint64_t digest = 1469598103934665603ULL;
static jmp_buf invalid_tag;
static bool expect_invalid;
static struct {
    Node * target;
    unsigned reads, updates;
    int32_t after_read, before_update;
} interleaving;

static Node * node(size_t p) {
    CHECK(p >= (size_t)nodes && p < (size_t)(nodes + N));
    CHECK((p - (size_t)nodes) % sizeof(Node) == 0);
    Node * o = (Node *)p;
    CHECK(!o->disposed);
    return o;
}

static Node * typed_node(size_t p, uint8_t tag) {
    Node * o = node(p);
    CHECK(o->tag == tag);
    return o;
}

static size_t field_count(Node * o) {
    CHECK(!o->count_read && !o->begin_read);
    o->count_read = true;
    return o->count;
}

static size_t field_begin(Node * o) {
    CHECK(o->count_read && !o->begin_read);
    o->begin_read = true;
    return (size_t)o->fields;
}

static inline uint32_t lean_gc_read_rc(size_t p) {
    Node * o = node(p);
    uint32_t rc = o->rc;
    if (o == interleaving.target && ++interleaving.reads == 1)
        o->rc += (uint32_t)interleaving.after_read;
    return rc;
}
static inline lean_object * lean_gc_write_rc(size_t p, uint32_t rc) {
    node(p)->rc = rc;
    return lean_box(0);
}
static inline uint32_t lean_gc_fetch_add_rc(size_t p) {
    Node * o = node(p);
    if (o == interleaving.target) {
        ++interleaving.updates;
        o->rc += (uint32_t)interleaving.before_update;
    }
    return o->rc++;
}
static inline size_t lean_gc_read_next(size_t p) { return node(p)->next; }
static inline lean_object * lean_gc_write_next(size_t p, size_t next) {
    node(p)->next = next;
    return lean_box(0);
}
static inline uint8_t lean_gc_read_tag(size_t p) { return node(p)->tag; }
static inline size_t lean_gc_ctor_count(size_t p) {
    Node * o = node(p);
    CHECK(o->tag <= LeanMaxCtorTag);
    return field_count(o);
}
static inline size_t lean_gc_ctor_begin(size_t p) {
    Node * o = node(p);
    CHECK(o->tag <= LeanMaxCtorTag);
    return field_begin(o);
}
static inline size_t lean_gc_closure_count(size_t p) {
    return field_count(typed_node(p, LeanClosure));
}
static inline size_t lean_gc_closure_begin(size_t p) {
    return field_begin(typed_node(p, LeanClosure));
}
static inline size_t lean_gc_array_count(size_t p) {
    return field_count(typed_node(p, LeanArray));
}
static inline size_t lean_gc_array_begin(size_t p) {
    return field_begin(typed_node(p, LeanArray));
}
static inline size_t lean_gc_ref_begin(size_t p) {
    Node * o = typed_node(p, LeanRef);
    CHECK(o->count == 1 && !o->count_read && !o->begin_read);
    o->begin_read = true;
    return (size_t)o->fields;
}
static inline size_t lean_gc_field_next(size_t cursor) { return cursor + sizeof(size_t); }
static inline size_t lean_gc_read_field(size_t cursor) {
    CHECK(cursor >= (size_t)nodes && cursor < (size_t)(nodes + N));
    Node * o = node((size_t)&nodes[(cursor - (size_t)nodes) / sizeof(Node)]);
    CHECK(cursor >= (size_t)o->fields && cursor < (size_t)(o->fields + o->count));
    CHECK((cursor - (size_t)o->fields) % sizeof(size_t) == 0);
    CHECK(o->begin_read && cursor == (size_t)&o->fields[o->fields_read]);
    ++o->fields_read;
    return *(size_t *)cursor;
}
static inline size_t lean_gc_read_thunk_closure(size_t p) {
    Node * o = node(p);
    CHECK(o->tag == LeanThunk && !o->closure_read);
    o->closure_read = true;
    ++o->fields_read;
    return o->fields[0];
}
static inline size_t lean_gc_read_thunk_value(size_t p) {
    Node * o = node(p);
    CHECK(o->tag == LeanThunk && o->closure_read && !o->value_read);
    o->value_read = true;
    ++o->fields_read;
    return o->fields[1];
}
static lean_object * record_disposal(Node * o) {
    CHECK(o->fields_read == o->count && actual_n < N);
    o->disposed = true;
    unsigned id = (unsigned)(o - nodes);
    actual[actual_n++] = id;
    digest = (digest ^ id) * 1099511628211ULL;
    return lean_box(0);
}
static inline lean_object * lean_gc_free_small(size_t p) {
    Node * o = node(p);
    CHECK(o->tag <= LeanMaxCtorTag || o->tag == LeanThunk || o->tag == LeanRef ||
          o->tag == LeanMPZ || o->tag == LeanExternal);
    if (o->tag <= LeanMaxCtorTag) CHECK(o->count_read && o->begin_read);
    if (o->tag == LeanThunk) CHECK(o->closure_read && o->value_read);
    if (o->tag == LeanRef) CHECK(o->begin_read);
    if (o->tag == LeanMPZ) CHECK(o->mpz_destroyed);
    if (o->tag == LeanExternal) CHECK(o->finalized);
    return record_disposal(o);
}
static inline lean_object * lean_gc_free_closure(size_t p) {
    Node * o = typed_node(p, LeanClosure);
    CHECK(o->count_read && o->begin_read);
    return record_disposal(o);
}
static inline lean_object * lean_gc_free_array(size_t p) {
    Node * o = typed_node(p, LeanArray);
    CHECK(o->count_read && o->begin_read);
    return record_disposal(o);
}
static inline lean_object * lean_gc_free_scalar_array(size_t p) {
    return record_disposal(typed_node(p, LeanScalarArray));
}
static inline lean_object * lean_gc_free_string(size_t p) {
    return record_disposal(typed_node(p, LeanString));
}
static inline lean_object * lean_gc_destroy_mpz(size_t p) {
    Node * o = typed_node(p, LeanMPZ);
    CHECK(!o->mpz_destroyed);
    o->mpz_destroyed = true;
    return lean_box(0);
}
static inline lean_object * lean_gc_deactivate_task(size_t p) {
    return record_disposal(typed_node(p, LeanTask));
}
static inline lean_object * lean_gc_deactivate_promise(size_t p) {
    return record_disposal(typed_node(p, LeanPromise));
}
static inline lean_object * lean_gc_finalize_external(size_t p) {
    Node * o = typed_node(p, LeanExternal);
    CHECK(!o->finalized);
    o->finalized = true;
    return lean_box(0);
}
static inline lean_object * lean_gc_unreachable(size_t p) {
    Node * o = node(p);
    CHECK(expect_invalid && (o->tag == LeanStructArray || o->tag == LeanReserved));
    longjmp(invalid_tag, 1);
}

#include "object_gc.inc"
#include "counted_edge_model.h"

static void compare(void) {
    CHECK(actual_n == expected_n);
    for (unsigned i = 0; i < actual_n; ++i) CHECK(actual[i] == expected[i]);
    for (unsigned i = 0; i < N; ++i) {
        CHECK(nodes[i].disposed == !live[i]);
        if (live[i]) CHECK((int32_t)nodes[i].rc == counts[i]);
    }
}

static void reset(void) {
    actual_n = expected_n = top = 0;
    interleaving.target = NULL;
    for (unsigned i = 0; i < N; ++i) {
        nodes[i] = (Node){.rc = 1};
        counts[i] = 1;
        live[i] = true;
        degree[i] = 0;
        for (unsigned f = 0; f < F; ++f) edges[i][f] = -1;
    }
}

static void graph_case(void) {
    static const uint8_t tags[] = {
        0, LeanMaxCtorTag, LeanPromise, LeanClosure, LeanArray, LeanScalarArray,
        LeanString, LeanMPZ, LeanThunk, LeanTask, LeanRef, LeanExternal
    };
    reset();
    rng = seed;
    unsigned roots[R];
    for (unsigned i = 0; i < N; ++i) roots[i] = i;
    for (unsigned i = N; i < R; ++i) ++counts[roots[i] = random32() % N];
    for (unsigned i = 0; i < N; ++i) {
        uint8_t tag = nodes[i].tag = tags[random32() % sizeof(tags)];
        degree[i] = tag <= LeanMaxCtorTag || tag == LeanClosure || tag == LeanArray
            ? random32() % (F + 1) : tag == LeanThunk ? 2 : tag == LeanRef ? 1 : 0;
        nodes[i].count = degree[i];
        for (unsigned f = 0; f < degree[i]; ++f) {
            unsigned target = random32() % (N + 4);
            if ((seed & 1) && target <= i) target = N;
            if (target < N) {
                edges[i][f] = (int)target;
                ++counts[target];
                nodes[i].fields[f] = (size_t)&nodes[target];
            } else {
                nodes[i].fields[f] = f % 2 == 0 ? 0 : (size_t)lean_box(f);
            }
        }
    }
    for (unsigned i = 0; i < N; ++i) {
        unsigned mode = random32() % 16;
        if (mode < 7) counts[i] = -counts[i];
        else if (mode == 7) counts[i] = 0;
        else if (mode == 8) counts[i] = LEAN_RC_STICKY_DROP;
        else if (mode == 9) counts[i] = LEAN_RC_STUCK_ST;
        nodes[i].rc = (uint32_t)counts[i];
    }
    for (unsigned i = R - 1; i > 0; --i) {
        unsigned j = random32() % (i + 1), tmp = roots[i];
        roots[i] = roots[j];
        roots[j] = tmp;
    }
    for (unsigned r = 0; r < R; ++r) {
        model_drop(roots[r], N);
        lean_gc_dec_ref_cold((size_t)&nodes[roots[r]]);
        compare();
    }
}

static void siblings(bool thunk) {
    reset();
    nodes[0].tag = thunk ? LeanThunk : 0;
    nodes[0].count = degree[0] = 2;
    for (unsigned f = 0; f < 2; ++f) {
        edges[0][f] = (int)f + 1;
        nodes[0].fields[f] = (size_t)&nodes[f + 1];
    }
    /* Only the parent owns the children: both must survive in the intrusive queue. */
    model_drop(0, N);
    lean_gc_dec_ref_cold((size_t)&nodes[0]);
    compare();
    CHECK(actual_n == 3 && actual[0] == 0 && actual[1] == 2 && actual[2] == 1);
}

static void dispatch_cases(void) {
    for (unsigned tag = 0; tag <= UINT8_MAX; ++tag) {
        if (tag == LeanStructArray || tag == LeanReserved) {
            reset();
            nodes[0].tag = (uint8_t)tag;
            expect_invalid = true;
            if (setjmp(invalid_tag) == 0) {
                lean_gc_dec_ref_cold((size_t)&nodes[0]);
                CHECK(false);
            }
            expect_invalid = false;
            CHECK(actual_n == 0 && !nodes[0].disposed);
            continue;
        }
        unsigned min = tag == LeanThunk ? 2 : tag == LeanRef ? 1 : 0;
        unsigned max = tag <= LeanMaxCtorTag || tag == LeanClosure || tag == LeanArray ? F : min;
        for (unsigned n = min; n <= max; ++n) {
            reset();
            nodes[0].tag = (uint8_t)tag;
            nodes[0].count = degree[0] = n;
            unsigned refs = 0;
            for (unsigned f = 0; f < n; ++f) {
                if (f % 3 == 0) {
                    edges[0][f] = 1;
                    nodes[0].fields[f] = (size_t)&nodes[1];
                    ++refs;
                } else {
                    nodes[0].fields[f] = f % 3 == 1 ? (size_t)lean_box(f) : 0;
                }
            }
            if (refs) nodes[1].rc = (uint32_t)(counts[1] = (int)refs);
            model_drop(0, N);
            lean_gc_dec_ref_cold((size_t)&nodes[0]);
            compare();
        }
    }
}

static void shared_interleavings(void) {
    static const struct {
        int32_t initial, after_read, before_update, result;
        bool last;
        unsigned updates;
    } cases[] = {
        {-2, 1, 0, 0, true, 1},
        {-2, 0, 1, 0, true, 1},
        {-3, 1, 1, 0, true, 1},
        {-2, -1, 0, -2, false, 1},
        {-3, 1, -1, -2, false, 1},
        {LEAN_RC_STICKY_DROP + 1, -2, 0, LEAN_RC_STICKY_DROP - 1, false, 0},
        {LEAN_RC_STICKY_DROP + 1, 0, -2, LEAN_RC_STICKY_DROP, false, 1},
        {LEAN_RC_STICKY_DROP, 0, 0, LEAN_RC_STICKY_DROP, false, 0},
    };
    /* Exercise the root, ordinary scanner, and direct unary continuation. */
    for (unsigned path = 0; path < 3; ++path) {
        for (unsigned i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
            reset();
            Node * target = &nodes[path == 0 ? 0 : 1];
            if (path != 0) {
                nodes[0].count = path == 1 ? 2 : 1;
                nodes[0].fields[0] = (size_t)target;
            }
            target->rc = (uint32_t)cases[i].initial;
            interleaving.target = target;
            interleaving.reads = interleaving.updates = 0;
            interleaving.after_read = cases[i].after_read;
            interleaving.before_update = cases[i].before_update;
            lean_gc_dec_ref_cold((size_t)&nodes[0]);
            CHECK((int32_t)target->rc == cases[i].result);
            CHECK(target->disposed == cases[i].last);
            CHECK(interleaving.updates == cases[i].updates);
            CHECK(actual_n == (path != 0) + (unsigned)cases[i].last);
        }
    }
}

int main(void) {
    dispatch_cases();
    siblings(false);
    siblings(true);
    shared_interleavings();
    for (seed = 1; seed <= 4096; ++seed) graph_case();
    printf("candidate: 256 tags, 24 shared interleavings, and 4096 graph cases; deletion trace %llx\n",
           (unsigned long long)digest);
    return 0;
}
