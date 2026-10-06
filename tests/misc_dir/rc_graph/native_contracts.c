/*
Runtime boundary regressions, using the public allocation/reference-count APIs.
Queue headers are observed by an earlier sibling's finalizer while their storage
is still allocated. No private collector helper or deletion algorithm is copied.
The promise cases require a runtime built with LEAN_MULTI_THREAD.
*/
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void);
/* Exported BaseIO primitives used by Init.System.Promise, absent from lean.h. */
lean_obj_res lean_io_promise_new(void);
lean_obj_res lean_io_promise_resolve(lean_obj_arg value, b_lean_obj_arg promise);
lean_obj_res lean_io_promise_result_opt(b_lean_obj_arg promise);

static char const * test_name;
#define CHECK(c) do { \
    if (!(c)) { \
        fprintf(stderr, "%s:%d: %s: %s\n", __FILE__, __LINE__, test_name, #c); \
        abort(); \
    } \
} while (0)

enum { MARKERS = 32, PROBE = 31 };
typedef struct {
    unsigned id;
    void (*hook)(void *);
    void * context;
} marker_data;

static marker_data markers[MARKERS];
static unsigned created[MARKERS], finalized[MARKERS], trace[MARKERS], trace_size;
static lean_external_class * marker_class;

static void finalize(void * data) {
    marker_data * m = data;
    CHECK(++finalized[m->id] == 1);
    CHECK(trace_size < MARKERS);
    trace[trace_size++] = m->id;
    if (m->hook) m->hook(m->context);
}

/* Markers own no Lean references; hook contexts are borrowed from the test. */
static void foreach(void * data, b_lean_obj_arg fn) { (void)data; (void)fn; }

static lean_object * marker(unsigned id) {
    CHECK(id < MARKERS && created[id]++ == 0);
    markers[id] = (marker_data){ .id = id };
    return lean_alloc_external(marker_class, &markers[id]);
}

static lean_object * probe(void (*hook)(void *), void * context) {
    lean_object * o = marker(PROBE);
    markers[PROBE].hook = hook;
    markers[PROBE].context = context;
    return o;
}

static void start(char const * name) {
    test_name = name;
    memset(created, 0, sizeof(created));
    memset(finalized, 0, sizeof(finalized));
    trace_size = 0;
}

static void finish(void) {
    for (unsigned i = 0; i < MARKERS; ++i) CHECK(finalized[i] == created[i]);
}

static void expect_trace(unsigned const * expected, size_t count) {
    CHECK(trace_size == count);
    for (size_t i = 0; i < count; ++i) CHECK(trace[i] == expected[i]);
}

static lean_obj_res never_called(lean_obj_arg a, lean_obj_arg b,
        lean_obj_arg c, lean_obj_arg d, lean_obj_arg e) {
    (void)a; (void)b; (void)c; (void)d; (void)e;
    CHECK(false);
    return lean_box(0);
}

static lean_obj_res never_forced(lean_obj_arg captured, lean_obj_arg unit) {
    (void)captured; (void)unit;
    CHECK(false);
    return lean_box(0);
}

static void scalar_pattern(lean_object * o) {
    for (unsigned i = 0; i < 16; ++i) lean_ctor_scalar_cptr(o)[i] = (uint8_t)(0xA0 + i);
}

static void check_scalar_pattern(lean_object * o) {
    for (unsigned i = 0; i < 16; ++i) CHECK(lean_ctor_scalar_cptr(o)[i] == 0xA0 + i);
}

enum { QUEUED = 8 };
typedef struct {
    lean_object * objects[QUEUED];
    unsigned char headers[QUEUED][8];
    lean_object * children[7];
    lean_object * thunk_closure;
    lean_object * capacity_canary;
} queue_context;

static void inspect_queue(void * data) {
    queue_context * q = data;
    for (unsigned i = 0; i < 7; ++i) CHECK(finalized[i] == 0);
    for (unsigned i = 0; i < QUEUED; ++i) {
        lean_object * o = q->objects[i];
        unsigned char header[8];
        uintptr_t stored;
        uintptr_t predecessor = i ? (uintptr_t)q->objects[i - 1] : 0;
        memcpy(header, o, sizeof(header));
        memcpy(&stored, o, sizeof(stored));
        CHECK(header[6] == q->headers[i][6] && header[7] == q->headers[i][7]);
        CHECK(lean_ptr_other(o) == header[6] && lean_ptr_tag(o) == header[7]);
        /* Observe the actual queue write, including its null terminator. */
        if (sizeof(void *) == 8) {
            CHECK(((uint64_t)predecessor >> 48) == 0);
            CHECK(((uint64_t)stored & UINT64_C(0x0000FFFFFFFFFFFF)) == predecessor);
        } else {
            CHECK(stored == predecessor);
            CHECK(memcmp(header + 4, q->headers[i] + 4, 4) == 0);
        }
    }

    lean_object * ctor = q->objects[0];
    CHECK(lean_ptr_tag(ctor) == LeanMaxCtorTag && lean_ctor_num_objs(ctor) == 4);
    CHECK(lean_ctor_get(ctor, 0) == q->children[0]);
    CHECK(lean_ctor_get(ctor, 1) == lean_box(UINTPTR_MAX >> 1));
    CHECK(lean_ctor_get(ctor, 2) == q->children[1] && lean_ctor_get(ctor, 3) == lean_box(0));
    check_scalar_pattern(ctor);

    lean_object * closure = q->objects[1];
    CHECK(lean_closure_fun(closure) == (void *)never_called);
    CHECK(lean_closure_arity(closure) == 5 && lean_closure_num_fixed(closure) == 4);
    CHECK(lean_closure_get(closure, 0) == q->children[2]);
    CHECK(lean_closure_get(closure, 1) == lean_box(23));
    CHECK(lean_closure_get(closure, 2) == lean_box(0));
    CHECK(lean_closure_get(closure, 3) == lean_box(0));

    lean_object * array = q->objects[2];
    CHECK(lean_array_size(array) == 5 && lean_array_capacity(array) == 8);
    CHECK(lean_array_is_marked_linear(array));
    CHECK(lean_array_get_core(array, 0) == lean_box(0));
    CHECK(lean_array_get_core(array, 1) == q->children[3]);
    CHECK(lean_array_get_core(array, 2) == lean_box(0));
    CHECK(lean_array_get_core(array, 3) == q->children[3]);
    CHECK(lean_array_get_core(array, 4) == lean_box(UINTPTR_MAX >> 1));
    for (size_t i = 5; i < 8; ++i) CHECK(lean_array_cptr(array)[i] == q->capacity_canary);

    CHECK(lean_to_ref(q->objects[3])->m_value == q->children[4]);
    CHECK(lean_to_thunk(q->objects[4])->m_closure == q->thunk_closure);
    CHECK(lean_to_thunk(q->objects[4])->m_value == NULL);
    CHECK(lean_to_thunk(q->objects[5])->m_closure == NULL);
    CHECK(lean_to_thunk(q->objects[5])->m_value == q->children[6]);
    CHECK(lean_sarray_elem_size(q->objects[6]) == 8);
    CHECK(lean_sarray_is_marked_linear(q->objects[6]));
    CHECK(lean_sarray_size(q->objects[6]) == 3 && lean_sarray_capacity(q->objects[6]) == 5);
    for (size_t i = 0; i < 24; ++i) CHECK(lean_sarray_cptr(q->objects[6])[i] == 0xAB);
    CHECK(strcmp(lean_string_cstr(q->objects[7]), "queued string") == 0);
}

static void queue_layout(void) {
    start("queue layout, physical slots and payload frame");
    uint16_t endian = 1;
    CHECK(sizeof(void *) == 4 || sizeof(void *) == 8);
    CHECK(sizeof(lean_object) == 8 && sizeof(uintptr_t) == sizeof(void *));
    CHECK(*(unsigned char *)&endian == 1);
    CHECK(lean_is_scalar(lean_box(UINTPTR_MAX >> 1)));
    CHECK(lean_unbox(lean_box(UINTPTR_MAX >> 1)) == UINTPTR_MAX >> 1);
    queue_context q;
    for (unsigned i = 0; i < 7; ++i) q.children[i] = marker(i);
    q.capacity_canary = marker(7);
    q.objects[0] = lean_alloc_ctor(LeanMaxCtorTag, 4, 16);
    lean_ctor_set(q.objects[0], 0, q.children[0]);
    lean_ctor_set(q.objects[0], 1, lean_box(UINTPTR_MAX >> 1));
    lean_ctor_set(q.objects[0], 2, q.children[1]);
    lean_ctor_set(q.objects[0], 3, lean_box(0));
    scalar_pattern(q.objects[0]);
    q.objects[1] = lean_alloc_closure((void *)never_called, 5, 4);
    lean_closure_set(q.objects[1], 0, q.children[2]);
    lean_closure_set(q.objects[1], 1, lean_box(23));
    lean_closure_set(q.objects[1], 2, lean_box(0));
    lean_closure_set(q.objects[1], 3, lean_box(0));
    q.objects[2] = lean_alloc_array(5, 8);
    lean_array_set_core(q.objects[2], 0, lean_box(0));
    lean_array_set_core(q.objects[2], 1, q.children[3]);
    lean_array_set_core(q.objects[2], 2, lean_box(0));
    lean_inc(q.children[3]);
    lean_array_set_core(q.objects[2], 3, q.children[3]);
    lean_array_set_core(q.objects[2], 4, lean_box(UINTPTR_MAX >> 1));
    /* Capacity slots are physical storage, but own no references beyond size. */
    for (size_t i = 5; i < 8; ++i) lean_array_cptr(q.objects[2])[i] = q.capacity_canary;
    lean_array_mark_linear_core(q.objects[2]);
    q.objects[3] = lean_st_mk_ref(q.children[4]);
    q.thunk_closure = lean_alloc_closure((void *)never_forced, 2, 1);
    lean_closure_set(q.thunk_closure, 0, q.children[5]);
    q.objects[4] = lean_mk_thunk(q.thunk_closure);
    q.objects[5] = lean_thunk_pure(q.children[6]);
    q.objects[6] = lean_alloc_sarray(8, 3, 5);
    memset(lean_sarray_cptr(q.objects[6]), 0xAB, 24);
    lean_sarray_mark_linear_core(q.objects[6]);
    q.objects[7] = lean_mk_string("queued string");

    lean_object * root = lean_alloc_ctor(0, QUEUED + 1, 0);
    for (unsigned i = 0; i < QUEUED; ++i) {
        CHECK((uintptr_t)q.objects[i] % sizeof(void *) == 0 && !lean_is_scalar(q.objects[i]));
        memcpy(q.headers[i], q.objects[i], 8);
        CHECK(q.headers[i][6] == lean_ptr_other(q.objects[i]));
        CHECK(q.headers[i][7] == lean_ptr_tag(q.objects[i]));
        lean_ctor_set(root, i, q.objects[i]);
    }
    lean_ctor_set(root, QUEUED, probe(inspect_queue, &q));
    lean_dec(root);
    unsigned const expected[] = { PROBE, 6, 5, 4, 3, 2, 1, 0 };
    expect_trace(expected, sizeof(expected) / sizeof(*expected));
    CHECK(finalized[7] == 0 && lean_internal_get_rc(q.capacity_canary) == 1);
    lean_dec(q.capacity_canary);

    /* No object references: physical count is nevertheless nonzero. */
    lean_object * scalar_only = lean_alloc_array(3, 9);
    for (size_t i = 0; i < 3; ++i) lean_array_set_core(scalar_only, i, lean_box(i));
    lean_dec(scalar_only);
    lean_dec(lean_alloc_array(0, 9));
    lean_dec(lean_alloc_closure((void *)never_forced, 2, 0));
    lean_dec(lean_st_mk_ref(NULL));
    lean_dec(lean_thunk_pure(lean_box(0)));
    finish();
}

typedef struct {
    lean_object * retained;
    lean_object * child;
    lean_object * nested;
    bool shared;
} frame_context;

static void check_retained(frame_context const * f) {
    CHECK(finalized[0] == 0);
    CHECK(lean_ptr_tag(f->retained) == 17 && lean_ctor_num_objs(f->retained) == 2);
    CHECK(lean_ctor_get(f->retained, 0) == f->child);
    CHECK(lean_ctor_get(f->retained, 1) == lean_box(UINTPTR_MAX >> 1));
    check_scalar_pattern(f->retained);
}

static void nested_finalizer(void * data) {
    frame_context * f = data;
    check_retained(f);
    CHECK(lean_internal_get_rc(f->retained) == (f->shared ? -3 : 3));
    CHECK(finalized[1] == 0); /* The outer queue is suspended during reentry. */
    lean_dec(f->nested);
    f->nested = NULL;
    CHECK(finalized[2] == 1);
    CHECK(lean_internal_get_rc(f->retained) == (f->shared ? -1 : 1));
    /* A finalizer may allocate and may recursively invoke task disposal. */
    lean_dec(lean_task_pure(marker(3)));
    lean_inc(f->retained);
    lean_dec(f->retained);
    check_retained(f);
}

static void retained_frame(bool shared) {
    start(shared ? "shared retained frame with reentrant finalizer" :
        "single-threaded retained frame with reentrant finalizer");
    frame_context f = { .shared = shared };
    f.child = marker(0);
    f.retained = lean_alloc_ctor(17, 2, 16);
    lean_ctor_set(f.retained, 0, f.child);
    lean_ctor_set(f.retained, 1, lean_box(UINTPTR_MAX >> 1));
    scalar_pattern(f.retained);
    if (shared) lean_mark_mt(f.retained);
    f.nested = lean_alloc_ctor(0, 3, 0);
    lean_inc(f.retained);
    lean_ctor_set(f.nested, 0, f.retained);
    lean_inc(f.retained);
    lean_ctor_set(f.nested, 1, f.retained);
    lean_ctor_set(f.nested, 2, marker(2));
    lean_object * outer = lean_alloc_ctor(0, 3, 0);
    lean_inc(f.retained);
    lean_ctor_set(outer, 0, f.retained);
    lean_ctor_set(outer, 1, marker(1));
    lean_ctor_set(outer, 2, probe(nested_finalizer, &f));
    lean_dec(outer);
    CHECK(f.nested == NULL);
    check_retained(&f);
    CHECK(lean_internal_get_rc(f.retained) == (shared ? -1 : 1));
    lean_dec(f.retained);
    unsigned const expected[] = { PROBE, 2, 3, 1, 0 };
    expect_trace(expected, sizeof(expected) / sizeof(*expected));
    finish();
}

static void finished_task(void) {
    start("finished task value ownership");
    lean_object * value = marker(0);
    lean_object * task = lean_task_pure(value);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_FINISHED);
    CHECK(lean_task_get(task) == value);
    lean_inc(task);
    lean_object * owned = lean_task_get_own(task);
    CHECK(owned == value && finalized[0] == 0);
    lean_dec(task);
    CHECK(finalized[0] == 0);
    lean_dec(owned);
    finish();
}

static void promise_results(void) {
    start("unresolved promise with surviving result task");
    lean_object * p = lean_io_promise_new();
    lean_object * task = lean_io_promise_result_opt(p);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_RUNNING);
    lean_dec(p);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_FINISHED);
    lean_object * none = lean_task_get_own(task);
    CHECK(none == lean_box(0));
    lean_dec(none);
    finish();

    start("resolved promise, duplicate resolve and owned result");
    p = lean_io_promise_new();
    task = lean_io_promise_result_opt(p);
    lean_object * value = marker(0);
    lean_dec(lean_io_promise_resolve(value, p));
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_FINISHED);
    lean_object * some = lean_task_get(task);
    CHECK(!lean_is_scalar(some) && lean_ptr_tag(some) == 1);
    CHECK(lean_ctor_get(some, 0) == value);
    lean_dec(lean_io_promise_resolve(marker(1), p));
    CHECK(finalized[1] == 1 && finalized[0] == 0);
    CHECK(lean_task_get(task) == some);
    lean_dec(p);
    CHECK(finalized[0] == 0);
    lean_object * owned = lean_task_get_own(task);
    CHECK(owned == some && lean_ctor_get(owned, 0) == value);
    CHECK(finalized[0] == 0);
    lean_dec(owned);
    finish();

    start("promise owns result after external result token is dropped");
    p = lean_io_promise_new();
    task = lean_io_promise_result_opt(p);
    lean_dec(task);
    lean_dec(lean_io_promise_resolve(marker(0), p));
    CHECK(finalized[0] == 0);
    lean_dec(p);
    finish();
}

static void capture_finalizer(void * data) {
    (void)data;
    /* Deadlock if deactivate_task releases its closure while holding the mutex. */
    lean_dec(lean_task_pure(marker(1)));
}

static void deferred_task(void) {
    start("waiting task deactivation releases captures and defers storage reclamation");
    lean_object * p = lean_io_promise_new();
    lean_object * dependency = lean_io_promise_result_opt(p);
    lean_object * captured = probe(capture_finalizer, NULL);
    lean_object * fn = lean_alloc_closure((void *)never_forced, 2, 1);
    lean_closure_set(fn, 0, captured);
    lean_object * task = lean_task_map_core(fn, dependency, 0, true, false);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_WAITING);
    lean_task_imp * imp = lean_to_task(task)->m_imp;
    lean_dec(task);
    CHECK(finalized[PROBE] == 1 && finalized[1] == 1);
    /*
    The live promise still owns dependency and keeps it unresolved, so its
    scheduler link retains this deactivated task. Dropping p may reclaim both;
    do not use these borrowed pointers afterward or change the task's dead RC.
    */
    CHECK(lean_to_task(dependency)->m_imp->m_head_dep == lean_to_task(task));
    CHECK(imp == lean_to_task(task)->m_imp);
    CHECK(imp->m_deleted && imp->m_canceled && imp->m_closure == NULL);
    lean_dec(p); /* Scheduler reclaims the deactivated dependent without executing fn. */
    finish();
}

static lean_obj_res map_none(lean_obj_arg retained, lean_obj_arg value) {
    CHECK(value == lean_box(0));
    CHECK(lean_ptr_tag(retained) == 17);
    check_scalar_pattern(retained);
    lean_dec(lean_task_pure(marker(1)));
    lean_dec(value);
    return retained;
}

static void promise_callback(void) {
    start("promise disposal runs a synchronous callback with retained state");
    lean_object * retained = lean_alloc_ctor(17, 1, 16);
    lean_ctor_set(retained, 0, marker(0));
    scalar_pattern(retained);
    lean_object * p = lean_io_promise_new();
    lean_object * fn = lean_alloc_closure((void *)map_none, 2, 1);
    lean_inc(retained);
    lean_closure_set(fn, 0, retained);
    lean_object * task = lean_task_map_core(fn, lean_io_promise_result_opt(p), 0, true, false);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_WAITING);
    lean_dec(p); /* Resolves none, executes map_none and reenters task disposal. */
    CHECK(finalized[1] == 1 && finalized[0] == 0);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_FINISHED);
    CHECK(lean_task_get(task) == retained);
    check_scalar_pattern(retained);
    lean_dec(task);
    CHECK(finalized[0] == 0 && lean_internal_get_rc(retained) == -1);
    lean_dec(retained);
    finish();
}

int main(void) {
    lean_initialize_runtime_module();
    marker_class = lean_register_external_class(finalize, foreach);
    queue_layout();
    retained_frame(false);
    retained_frame(true);
    finished_task();
    lean_init_task_manager_using(1);
    finished_task();
    promise_results();
    deferred_task();
    promise_callback();
    lean_finalize_task_manager();
    puts("native primitive contracts: queue, frame, reentry, task and promise cases passed");
    return 0;
}
