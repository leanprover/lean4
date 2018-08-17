/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include <algorithm>
#include <map>
#include <unordered_set>
#include <deque>
#include "runtime/stackinfo.h"
#include "runtime/object.h"
#include "runtime/utf8.h"
#include "runtime/apply.h"
#include "runtime/flet.h"
#include "runtime/interrupt.h"

namespace lean {
size_t obj_byte_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return cnstr_byte_size(o);
    case object_kind::Closure:         return closure_byte_size(o);
    case object_kind::Array:           return array_byte_size(o);
    case object_kind::ScalarArray:     return sarray_byte_size(o);
    case object_kind::String:          return string_byte_size(o);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::Task:            return sizeof(task_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

size_t obj_header_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return sizeof(constructor_object);
    case object_kind::Closure:         return sizeof(closure_object);
    case object_kind::Array:           return sizeof(array_object);
    case object_kind::ScalarArray:     return sizeof(sarray_object);
    case object_kind::String:          return sizeof(string_object);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::Task:            return sizeof(task_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the field m_rc to implement a linked list of lean objects to be deleted.
   This hack is safe because m_rc has type uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(object*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size"); // NOLINT

inline object * get_next(object * o) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    return *reinterpret_cast<object**>(o);
}

inline void set_next(object * o, object * n) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    *reinterpret_cast<object**>(o) = n;
}

inline void push_back(object * & todo, object * v) {
    set_next(v, todo);
    todo = v;
}

inline object * pop_back(object * & todo) {
    object * r = todo;
    todo = get_next(todo);
    return r;
}

inline void dec(object * o, object* & todo) {
    if (!is_scalar(o) && dec_ref_core(o))
        push_back(todo, o);
}

void del(object * o) {
    object * todo = nullptr;
    while (true) {
        switch (get_kind(o)) {
        case object_kind::Constructor: {
            object ** it  = cnstr_obj_cptr(o);
            object ** end = it + cnstr_num_objs(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::Closure: {
            object ** it  = closure_arg_cptr(o);
            object ** end = it + closure_num_fixed(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::Array: {
            object ** it  = array_cptr(o);
            object ** end = it + array_size(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::ScalarArray:
            free(o); break;
        case object_kind::String:
            free(o); break;
        case object_kind::MPZ:
            dealloc_mpz(o); break;
        case object_kind::Thunk:
            if (object * c = to_thunk(o)->m_closure) dec(c, todo);
            if (object * v = to_thunk(o)->m_value) dec(v, todo);
            free(o);
            break;
        case object_kind::Task:
            if (object * c = to_task(o)->m_closure) dec(c, todo);
            if (object * v = to_task(o)->m_value) dec(v, todo);
            dec(to_task(o)->m_reverse_deps, todo);
            dealloc_task(o);
            break;
        case object_kind::External:
            dealloc_external(o); break;
        }
        /* We can use a counter to avoid pauses at `del` when many objects
           are reachable from `o` need to be deleted.
           The idea is to have a threshold on the maximum number of elements
           that can be deleted in a single round. */
        if (todo == nullptr)
            return;
        o = pop_back(todo);
    }
}

/* Scalar arrays */

#if 0
static object * sarray_ensure_capacity(object * o, size_t extra) {
    lean_assert(!is_shared(o));
    size_t sz  = sarray_size(o);
    size_t cap = sarray_capacity(o);
    if (sz + extra > cap) {
        unsigned esize = sarray_elem_size(o);
        object * new_o = alloc_sarray(esize, sz, cap + sz + extra);
        lean_assert(sarray_capacity(new_o) >= sz + extra);
        memcpy(sarray_cptr<char>(new_o), sarray_cptr<char>(o), esize * sz);
        free(o);
        return new_o;
    } else {
        return o;
    }
}
#endif

/* Strings */
static inline char * w_string_data(object * o) { lean_assert(is_string(o)); return reinterpret_cast<char *>(o) + sizeof(string_object); }

static object * string_ensure_capacity(object * o, size_t extra) {
    lean_assert(!is_shared(o));
    size_t sz  = string_size(o);
    size_t cap = string_capacity(o);
    if (sz + extra > cap) {
        object * new_o = alloc_string(sz, cap + sz + extra, string_len(o));
        lean_assert(string_capacity(new_o) >= sz + extra);
        memcpy(w_string_data(new_o), string_data(o), sz);
        free(o);
        return new_o;
    } else {
        return o;
    }
}

object * mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_data(r), s, sz+1);
    return r;
}

object * mk_string(std::string const & s) {
    size_t sz  = s.size();
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_data(r), s.data(), sz);
    w_string_data(r)[sz] = 0;
    return r;
}

object * string_push(object * s, unsigned c) {
    lean_assert(!is_shared(s));
    object * r = string_ensure_capacity(s, 5);
    size_t sz  = string_size(r);
    unsigned consumed = push_unicode_scalar(w_string_data(r) + sz - 1, c);
    to_string(r)->m_size   = sz + consumed;
    to_string(r)->m_length++;
    w_string_data(r)[sz + consumed - 1] = 0;
    return r;
}

object * string_append(object * s1, object * s2) {
    lean_assert(!is_shared(s1));
    lean_assert(s1 != s2);
    size_t sz1 = string_size(s1);
    size_t sz2 = string_size(s2);
    size_t len1 = string_len(s1);
    size_t len2 = string_len(s2);
    object * r = string_ensure_capacity(s1, sz2-1);
    memcpy(w_string_data(r) + sz1 - 1, string_data(s2), sz2 - 1);
    unsigned new_sz = sz1 + sz2 - 1;
    to_string(r)->m_size   = new_sz;
    to_string(r)->m_length = len1 + len2;
    w_string_data(r)[new_sz - 1] = 0;
    return r;
}

bool string_eq(object * s1, object * s2) {
    if (string_size(s1) != string_size(s2))
        return false;
    return std::memcmp(string_data(s1), string_data(s2), string_size(s1)) == 0;
}

bool string_eq(object * s1, char const * s2) {
    if (string_size(s1) != strlen(s2) + 1)
        return false;
    return std::memcmp(string_data(s1), s2, string_size(s1)) == 0;
}

bool string_lt(object * s1, object * s2) {
    size_t sz1 = string_size(s1) - 1; // ignore null char in the end
    size_t sz2 = string_size(s2) - 1; // ignore null char in the end
    int r      = std::memcmp(string_data(s1), string_data(s2), std::min(sz1, sz2));
    return r < 0 || (r == 0 && sz1 < sz2);
}

/* Closures */

typedef object * (*lean_cfun2)(object *, object *); // NOLINT
typedef object * (*lean_cfun3)(object *, object *, object *); // NOLINT

static obj_res mk_closure_2_1(lean_cfun2 fn, obj_arg a) {
    object * c = alloc_closure(reinterpret_cast<lean_cfun>(fn), 2, 1);
    closure_set_arg(c, 0, a);
    return c;
}

static obj_res mk_closure_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    object * c = alloc_closure(reinterpret_cast<lean_cfun>(fn), 3, 2);
    closure_set_arg(c, 0, a1);
    closure_set_arg(c, 1, a2);
    return c;
}

/* Thunks */

static obj_res mk_thunk_3_2(lean_cfun3 fn, obj_arg a1, obj_arg a2) {
    return mk_thunk(mk_closure_3_2(fn, a1, a2));
}

b_obj_res thunk_get_core(b_obj_arg t) {
    object * c = to_thunk(t)->m_closure.exchange(nullptr);
    if (c != nullptr) {
        /* Recall that a closure uses the standard calling convention.
           `thunk_get` "consumes" the result `r` by storing it at `to_thunk(t)->m_value`.
           Then, it returns a reference to this result to the caller.
           The behavior is compatible with `cnstr_obj` with also returns a reference
           to be object stored in the constructor object.

           Recall that `apply_1` also consumes `c`'s RC. */
        object * r = apply_1(c, box(0));
        lean_assert(r != nullptr); /* Closure must return a valid lean object */
        lean_assert(to_thunk(t)->m_value == nullptr);
        to_thunk(t)->m_value = r;
        return r;
    } else {
        lean_assert(c == nullptr);
        /* There is another thread executing the closure. We keep waiting for the m_value to be
           set by another thread. */
        while (!to_thunk(t)->m_value) {
            this_thread::yield();
        }
        return to_thunk(t)->m_value;
    }
}

static obj_res thunk_map_fn_closure(obj_arg f, obj_arg t, obj_arg /* u */) {
    b_obj_res v = thunk_get(t);
    inc(v);
    obj_res r = apply_1(f, v);
    dec(v);
    return r;
}

obj_res thunk_map(obj_arg f, obj_arg t) {
    lean_assert(is_closure(f));
    lean_assert(is_thunk(t));
    return mk_thunk_3_2(thunk_map_fn_closure, f, t);
}

static obj_res thunk_bind_fn_closure(obj_arg x, obj_arg f, obj_arg /* u */) {
    b_obj_res v = thunk_get(x);
    inc(v);
    obj_res r = apply_1(f, v);
    dec(x);
    return r;
}

obj_res thunk_bind(obj_arg x, obj_arg f) {
    return mk_thunk_3_2(thunk_bind_fn_closure, x, f);
}

/* Tasks */

constexpr chrono::milliseconds g_worker_max_idle_time = chrono::milliseconds(1000);

LEAN_THREAD_PTR(task_object, g_current_task_object);

struct scoped_current_task_object : flet<task_object *> {
    scoped_current_task_object(task_object * t):flet(g_current_task_object, t) {}
};

class task_manager {
    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        task_object *            m_task;
    };
    typedef std::vector<worker_info *> workers;

    mutex                                         m_mutex;
    unsigned                                      m_workers_to_be_created;
    workers                                       m_workers;
    std::map<unsigned, std::deque<task_object *>> m_queue;
    condition_variable                            m_queue_cv;
    bool                                          m_shutting_down{false};


    task_object * dequeue() {
        lean_assert(!m_queue.empty());
        auto it                   = m_queue.begin();
        auto & highest_prio_deque = it->second;
        task_object * result      = highest_prio_deque.front();
        highest_prio_deque.pop_front();
        if (highest_prio_deque.empty())
            m_queue.erase(it);
        return result;
    }

    void enqueue_core(task_object * t) {
        inc_ref(t);
        m_queue[t->m_prio].push_back(t);
        if (m_workers_to_be_created > 0)
            spawn_worker();
        else
            m_queue_cv.notify_one();
    }

    void spawn_worker() {
        lean_assert(m_workers_to_be_created > 0);
        worker_info * this_worker = new worker_info();
        m_workers.push_back(this_worker);
        m_workers_to_be_created--;
        this_worker->m_thread.reset(new lthread([this, this_worker]() {
                    save_stack_info(false);
                    unique_lock<mutex> lock(m_mutex);
                    while (true) {
                        if (m_shutting_down) {
                            break;
                        }

                        if (m_queue.empty()) {
                            m_queue_cv.wait_for(lock, g_worker_max_idle_time);
                            continue;
                        }

                        task_object * t = dequeue();
                        lean_assert(get_rc(t) > 0);
                        reset_heartbeat();
                        object * v = nullptr;
                        {
                            flet<task_object *> update_task(this_worker->m_task, t);
                            scoped_current_task_object scope_cur_task(t);
                            object * c = t->m_closure;
                            t->m_closure = nullptr;
                            lock.unlock();
                            v = apply_1(c, box(0));
                            lock.lock();
                        }
                        if (v != nullptr) {
                            lean_assert(t->m_closure == nullptr);
                            t->m_value   = v;
                            handle_finished(t);
                        }
                        reset_heartbeat();
                    }

                    run_thread_finalizers();
                    run_post_thread_finalizers();
                }));
    }

    void handle_finished(task_object * t) {
        object * rev_deps = t->m_reverse_deps;
        t->m_reverse_deps = box(0);

        while (!is_scalar(rev_deps)) {
            object * head = cnstr_obj(rev_deps, 0);
            object * tail = cnstr_obj(rev_deps, 1);
            lean_assert(is_task(head));
            if (t->m_interrupted)
                to_task(head)->m_interrupted = true;
            enqueue_core(to_task(head));
            dec_ref(head);
            free(rev_deps);
            rev_deps = tail;
        }

        if (t->m_finished_cv)
            t->m_finished_cv->notify_all();

        dec_ref(t);
    }

public:
    task_manager(unsigned num_workers):
        m_workers_to_be_created(num_workers) {
    }

    ~task_manager() {
        {
            unique_lock<mutex> lock(m_mutex);
            for (worker_info * info : m_workers) {
                if (info->m_task)
                    info->m_task->m_interrupted = true;
            }
            m_shutting_down = true;
            m_queue_cv.notify_all();
        }
        for (worker_info * w : m_workers) {
            w->m_thread->join();
            delete w;
        }
        for (std::pair<const unsigned, std::deque<task_object *>> & entry : m_queue) {
            for (task_object * o : entry.second) {
                dec_ref(o);
            }
        }
    }

    void enqueue(task_object * t) {
        unique_lock<mutex> lock(m_mutex);
        enqueue_core(t);
    }

    void add_dep(task_object * t1, task_object * t2) {
        if (t1->m_value) {
            enqueue(t2);
            return;
        }
        unique_lock<mutex> lock(m_mutex);
        if (t1->m_value) {
            enqueue_core(t2);
            return;
        }
        object * new_list = alloc_cnstr(1, 2, 0);
        inc_ref(t2);
        cnstr_set_obj(new_list, 0, t2);
        cnstr_set_obj(new_list, 1, t1->m_reverse_deps);
        t1->m_reverse_deps = new_list;
    }

    void wait_for(task_object * t) {
        if (t->m_value)
            return;
        unique_lock<mutex> lock(m_mutex);
        if (t->m_finished_cv == nullptr)
            t->m_finished_cv = new condition_variable();
        t->m_finished_cv->wait(lock, [&]() { return t->m_value != nullptr; });
    }
};

static task_manager * g_task_manager = nullptr;

scoped_task_manager::scoped_task_manager(unsigned num_workers) {
    lean_assert(g_task_manager == nullptr);
#if defined(LEAN_MULTI_THREAD)
    g_task_manager = new task_manager(num_workers);
#endif
}

scoped_task_manager::~scoped_task_manager() {
    if (g_task_manager) {
        delete g_task_manager;
        g_task_manager = nullptr;
    }
}

task_object::task_object(obj_arg c, unsigned prio):
    object(object_kind::Task), m_closure(c), m_value(nullptr), m_reverse_deps(box(0)), m_prio(prio), m_interrupted(false) {
    lean_assert(is_closure(c));
}

task_object::task_object(obj_arg v):
    object(object_kind::Task), m_closure(nullptr), m_value(v), m_reverse_deps(box(0)), m_prio(0), m_interrupted(false) {
}

task_object::~task_object() {
    if (m_finished_cv)
        delete m_finished_cv;
}

static task_object * alloc_task(obj_arg c, unsigned prio) {
    return new task_object(c, prio); // NOLINT
}

static task_object * alloc_task(obj_arg v) {
    return new task_object(v); // NOLINT
}

obj_res task_start(obj_arg c, unsigned prio) {
    if (!g_task_manager) {
        return mk_thunk(c);
    } else {
        task_object * new_task = alloc_task(c, prio);
        g_task_manager->enqueue(new_task);
        return new_task;
    }
}

obj_res task_pure(obj_arg a) {
    if (!g_task_manager) {
        return mk_thunk_from_value(a);
    } else {
        return alloc_task(a);
    }
}

static obj_res task_map_fn(obj_arg f, obj_arg t, obj_arg) {
    lean_assert(to_task(t)->m_value);
    b_obj_res v = to_task(t)->m_value;
    inc(v);
    dec_ref(t);
    return apply_1(f, v);
}

obj_res task_map(obj_arg f, obj_arg t, unsigned prio) {
    if (!g_task_manager) {
        return thunk_map(f, t);
    } else {
        task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), prio);
        g_task_manager->add_dep(to_task(t), new_task);
        return new_task;
    }
}

b_obj_res task_get(b_obj_arg t) {
    if (!g_task_manager) {
        return thunk_get(t);
    } else {
        if (object * v = to_task(t)->m_value)
            return v;
        inc_ref(t);
        g_task_manager->wait_for(to_task(t));
        lean_assert(to_task(t)->m_value != nullptr);
        object * r = to_task(t)->m_value;
        dec_ref(t);
        return r;
    }
}

static obj_res task_bind_fn2(obj_arg t, obj_arg) {
    lean_assert(to_task(t)->m_value);
    b_obj_res v = to_task(t)->m_value;
    inc(v);
    dec_ref(t);
    return v;
}

static obj_res task_bind_fn1(obj_arg x, obj_arg f, obj_arg) {
    b_obj_res v = to_task(x)->m_value;
    inc(v);
    dec_ref(x);
    obj_res new_task          = apply_1(f, v);
    lean_assert(g_current_task_object->m_closure == nullptr);
    g_current_task_object->m_closure = mk_closure_2_1(task_bind_fn2, new_task);
    g_task_manager->add_dep(to_task(new_task), g_current_task_object);
    /* add_dep increased new_task's RC. Thus, since we don't return new_task,
       we must consume its RC */
    dec_ref(new_task);
    return nullptr; /* notify queue that task did not finish yet. */
}

obj_res task_bind(obj_arg x, obj_arg f, unsigned prio) {
    if (!g_task_manager) {
        return thunk_bind(x, f);
    } else {
        task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), prio);
        g_task_manager->add_dep(to_task(x), new_task);
        return new_task;
    }
}

/* Natural numbers */

object * nat_big_add(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) + unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) + mpz_value(a2));
}

object * nat_big_sub(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return box(0);
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return mk_nat_obj(mpz_value(a1) - unbox(a2));
    } else {
        if (mpz_value(a1) < mpz_value(a2))
            return box(0);
        else
            return mk_nat_obj(mpz_value(a1) - mpz_value(a2));
    }
}

object * nat_big_mul(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) * unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) * mpz_value(a2));
}

object * nat_big_div(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(unbox(a1) / mpz_value(a2) == 0);
        return box(0);
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : mk_nat_obj(mpz_value(a1) / n2);
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) / mpz_value(a2));
    }
}

object * nat_big_mod(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : box((mpz_value(a1) % mpz(n2)).get_unsigned_int());
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) % mpz_value(a2));
    }
}

bool nat_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != unbox(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool nat_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2))
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool nat_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

object * nat_big_land(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) & mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) & mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) & mpz_value(a2));
}

object * nat_big_lor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) | mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) | mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) | mpz_value(a2));
}

object * nat_big_lxor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) ^ mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) ^ mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) ^ mpz_value(a2));
}

/* Integers */

object * int_big_add(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) + int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) + mpz_value(a2));
}

object * int_big_sub(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) - mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) - int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) - mpz_value(a2));
}

object * int_big_mul(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) * int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) * mpz_value(a2));
}

object * int_big_div(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) / mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) / int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) / mpz_value(a2));
}

object * int_big_rem(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(mpz(int2int(a1)) % mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) % mpz(int2int(a2)));
    else
        return mk_int_obj(mpz_value(a1) % mpz_value(a2));
}

bool int_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(int2int(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != int2int(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool int_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) <= mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) <= int2int(a2);
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool int_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) < mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) < int2int(a2);
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

/* Debugging helper functions */

void dbg_print_str(object * o) {
    lean_assert(is_string(o));
    std::cout << string_data(o) << "\n";
}

void dbg_print_num(object * o) {
    if (is_scalar(o)) {
        std::cout << unbox(o) << "\n";
    } else {
        std::cout << mpz_value(o) << "\n";
    }
}
}

extern "C" void lean_dbg_print_str(lean::object* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::object* o) { lean::dbg_print_num(o); }
