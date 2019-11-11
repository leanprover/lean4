/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <random>
#include <iostream>
#include <vector>
#include "util/test.h" // <<< comment this list for performance experiments
#include "util/timeit.h"
#include "runtime/stackinfo.h"
#include "runtime/thread.h"
#include "runtime/serializer.h"
#include "runtime/sstream.h"
#include "util/object_ref.h"
#include "util/array_ref.h"
#include "util/init_module.h"
#include "util/nat.h"
using namespace lean;

#define USED(x) (void)(x)

object * f(object *) {
    std::cout << "executing f...\n";
    return box(10);
}

void tst1() {
    object_ref t(mk_thunk(alloc_closure(f, 0)));
    object * r1 = thunk_get(t.raw());
    object * r2 = thunk_get(t.raw());
    std::cout << "thunk value: " << unbox(r1) << "\n";
    std::cout << "thunk value: " << unbox(r2) << "\n";
}

static unsigned g_g_counter = 0;

object * g(object *) {
    g_g_counter++;
    return box(g_g_counter);
}

void tst2() {
    object * c = alloc_closure(g, 0);
    inc(c);
    object * r1 = apply_1(c, box(0));
    inc(c);
    object * r2 = apply_1(c, box(0));
    lean_assert(unbox(r1) == 1);
    lean_assert(unbox(r2) == 2);
    object_ref t(mk_thunk(c));
    object * r3 = thunk_get(t.raw());
    object * r4 = thunk_get(t.raw());
    lean_assert(unbox(r3) == 3);
    lean_assert(unbox(r4) == 3);
    USED(r1); USED(r2); USED(r3); USED(r4);
}

static unsigned g_h_counter = 0;

object * h(object *) {
    g_h_counter++;
    return box(0);
}

/* Make sure box(0) is not mistaken by cached value has not been initialized yet.

   The thunk implementation relies on the fact that nullptr is not a scalar nor a valid
   Lean object. */
void tst3() {
    object_ref t(mk_thunk(alloc_closure(h, 0)));
    lean_assert(g_h_counter == 0);
    object * r3 = thunk_get(t.raw());
    lean_assert(g_h_counter == 1);
    object * r4 = thunk_get(t.raw());
    lean_assert(g_h_counter == 1);
    lean_assert(unbox(r3) == 0);
    lean_assert(unbox(r4) == 0);
    USED(r3); USED(r4);
}

object * r(object *) {
    return mk_string("hello world");
}

void tst4() {
    object_ref t(mk_thunk(alloc_closure(r, 0)));
    object * r3  = thunk_get(t.raw());
    object * r4  = thunk_get(t.raw());
    lean_assert(string_eq(r3, "hello world"));
    lean_assert(string_eq(r4, "hello world"));
    USED(r3); USED(r4);
}

void tst5() {
    object_ref t(mk_thunk(alloc_closure(r, 0)));
    std::ostringstream out;
    serializer s(out);
    object_ref o(mk_string("bla bla"));
    s.write_object(o.raw());
    s.write_object(t.raw());
    s.write_object(t.raw());
    std::istringstream in(out.str());
    deserializer d(in);
    d.read_object();
    object * r1 = d.read_object();
    object * r2 = d.read_object();
    lean_assert(r1 == r2);
    lean_assert(is_thunk(r1));
    object * str = thunk_get(r1);
    lean_assert(strcmp(string_cstr(str), "hello world") == 0);
    USED(r2); USED(str);
}

unsigned g_counter = 0;
mutex g_io_mutex;

void show_msg(char const * msg) {
    unique_lock<mutex> lock(g_io_mutex);
    std::cout << msg;
}

object * task1_fn(object *) {
    g_counter++;
    show_msg("task 1 - started\n");
    this_thread::sleep_for(std::chrono::milliseconds(100));
    show_msg("task 1 - executed\n");
    return box(10);
}

object * add_10(object * a) {
    show_msg("task 2 - started\n");
    this_thread::sleep_for(std::chrono::milliseconds(200));
    show_msg("task 2 - executed\n");
    return box(unbox(a) + 10);
}

obj_res task3_fn(obj_arg val, obj_arg) {
    show_msg("task 3 - started\n");
    this_thread::sleep_for(std::chrono::milliseconds(100));
    show_msg("task 3 - executed\n");
    return box(unbox(val)+100);
}

obj_res mk_task3_fn(obj_arg val) {
    object * c     = alloc_closure(task3_fn, 1);
    closure_set(c, 0, val);
    return mk_task(c);
}

obj_res mk_task2(b_obj_arg task1) {
    inc(task1);
    return task_map(alloc_closure(add_10, 0), task1);
}

obj_res mk_task3(b_obj_arg task1) {
    inc_ref(task1);
    return task_bind(task1, alloc_closure(mk_task3_fn, 0));
}

void tst6_core(object * task1) {
    object_ref task2(mk_task2(task1));
    object_ref task3(mk_task3(task1));
    std::cout << "tst6 started...\n";
    object * r1 = task_get(task2.raw());
    object * r2 = task_get(task3.raw());
    std::cout << "r1: " << unbox(r1) << "\n";
    std::cout << "r2: " << unbox(r2) << "\n";
    lean_assert(unbox(r1) == 20);
    lean_assert(unbox(r2) == 110);
}

void tst6() {
    {
        scoped_task_manager m(8);
        object_ref task1(mk_task(alloc_closure(task1_fn, 0)));
        tst6_core(task1.raw());
    }
    {
        scoped_task_manager m(8);
        object_ref task1(task_pure(box(10)));
        tst6_core(task1.raw());
    }
    {
        scoped_task_manager m(8);
        object_ref task1(thunk_pure(box(10)));
        lean_assert(unbox(task_get(task1.raw())) == 10);
        lean_assert(io_has_finished_core(task1.raw()));
        tst6_core(task1.raw());
    }
    {
        scoped_task_manager m(8);
        object_ref task1(mk_thunk(alloc_closure(f, 0)));
        lean_assert(io_has_finished_core(task1.raw()));
        tst6_core(task1.raw());
    }
}

obj_res task4_fn(obj_arg) {
    show_msg("task 4 started...\n");
    while (!io_check_interrupt_core()) {
        show_msg("task 4 loop...\n");
        this_thread::sleep_for(std::chrono::milliseconds(10));
    }
    show_msg("task 4 was interrupted...\n");
    return box(1);
}

void tst7() {
    scoped_task_manager m(8);
    std::cout << ">> tst7 started...\n";
    object_ref task4(mk_task(alloc_closure(task4_fn, 0)));
    std::cout << "task4 has finished: " << io_has_finished_core(task4.raw()) << "\n";
    this_thread::sleep_for(std::chrono::milliseconds(100));
    show_msg("request interrupt...\n");
    io_request_interrupt_core(task4.raw());
    object * r = task_get(task4.raw());
    std::cout << "task4 has finished after get: " << io_has_finished_core(task4.raw()) << "\n";
    std::cout << "r: " << unbox(r) << "\n";
}

obj_res task5_fn(obj_arg id, obj_arg) {
    show_msg((sstream() << "task 5[" << unbox(id) << "] started \n").str().c_str());
    this_thread::sleep_for(std::chrono::milliseconds(10));
    show_msg((sstream() << "task 5[" << unbox(id) << "] finished \n").str().c_str());
    return id;
}

obj_res mk_task5(obj_arg id) {
    object * c = alloc_closure(task5_fn, 1);
    closure_set(c, 0, id);
    return mk_task(c);
}

void tst8() {
    scoped_task_manager m(8);
    std::cout << ">> tst8 started...\n";
    std::vector<object_ref> tasks;
    for (unsigned i = 0; i < 100; i++) {
        tasks.push_back(object_ref(mk_task5(box(i))));
    }
    unsigned i = 0;
    for (object_ref const & t : tasks) {
        object * r = task_get(t.raw());
        lean_assert(unbox(r) == i);
        i++;
    }
}

obj_res loop_until_interrupt_fn(obj_arg) {
    while (!io_check_interrupt_core()) {
        this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    return box(0);
}

obj_res task6_fn(obj_arg) {
    show_msg("task 6 started...\n");
    this_thread::sleep_for(std::chrono::milliseconds(100));
    show_msg("task 6 done...\n");
    return box(42);
}

obj_res mk_cons(b_obj_arg h, obj_arg t) {
    object * r = alloc_cnstr(1, 2, 0);
    inc(h);
    cnstr_set(r, 0, h);
    cnstr_set(r, 1, t);
    return r;
}

void tst9() {
    scoped_task_manager m(8);
    std::cout << ">> tst9 started...\n";
    object_ref t1(mk_task(alloc_closure(loop_until_interrupt_fn, 0)));
    object_ref t2(mk_task(alloc_closure(loop_until_interrupt_fn, 0)));
    object_ref t3(mk_task(alloc_closure(task6_fn, 0)));
    object_ref ts(mk_cons(t1.raw(), mk_cons(t2.raw(), mk_cons(t3.raw(), box(0)))));
    show_msg("invoke wait_any...\n");
    object * t = io_wait_any_core(ts.raw());
    show_msg("wait_any returned...\n");
    object * v = task_get(t);
    lean_assert(unbox(v) == 42);
    io_request_interrupt_core(t1.raw());
    io_request_interrupt_core(t2.raw());
    task_get(t1.raw());
    task_get(t2.raw());
}

void tst10() {
    scoped_task_manager m(8);
    std::cout << ">> tst10 started...\n";
    object_ref t1(mk_task(alloc_closure(task6_fn, 0)));
    {
        object_ref t2(mk_task2(t1.raw()));
    }
    task_get(t1.raw());
}

void tst11() {
    std::cout << ">> tst11 started...\n";
    {
        scoped_task_manager m(2);
        std::vector<object_ref> tasks;
        for (unsigned i = 0; i < 100; i++) {
            tasks.push_back(object_ref(mk_task(alloc_closure(loop_until_interrupt_fn, 0))));
        }
        this_thread::sleep_for(std::chrono::milliseconds(100));
    }
    std::cout << "tst11 done...\n";
}

static atomic<bool> g_finished;

obj_res loop_until_interrupt_fn2(obj_arg) {
    while (!io_check_interrupt_core()) {
        this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    g_finished = true;
    return box(0);
}


void tst12() {
    std::cout << ">> tst12 started...\n";
    g_finished = false;
    scoped_task_manager m(8);
    {
        object_ref t(mk_task(alloc_closure(loop_until_interrupt_fn2, 0)));
        this_thread::sleep_for(std::chrono::milliseconds(10));
        /* task t must be interrupted automatically */
    }
    while (g_finished) {
        this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    std::cout << "tst12 done...\n";
}


static atomic<unsigned> g_task7_counter(1);

obj_res task7_fn(obj_arg val, obj_arg) {
    if (g_task7_counter % 10 == 0)
        show_msg((sstream() << "task 7[" << g_task7_counter << "]\n").str().c_str());
    g_task7_counter++;
    this_thread::sleep_for(std::chrono::milliseconds(1));
    return box(unbox(val)+1);
}

obj_res mk_task7_fn(obj_arg val) {
    object * c     = alloc_closure(task7_fn, 1);
    closure_set(c, 0, val);
    return mk_task(c);
}

obj_res mk_task7(obj_arg t) {
    return task_bind(t, alloc_closure(mk_task7_fn, 0));
}

object * mul2(object * a) {
    return box(unbox(a) * 2);
}

void tst13() {
    scoped_task_manager m(8);
    std::cout << "tst13 started ...\n";
    object * curr = mk_task(alloc_closure(task1_fn, 0));
    std::vector<object *> children;
    for (unsigned i = 0; i < 1000; i++) {
        curr = mk_task7(curr);
        inc(curr);
        children.push_back(task_map(alloc_closure(mul2, 0), curr));
    }
    inc(curr);
    object * it = curr;
    for (unsigned i = 0; i < 10000; i++) {
        it = mk_task7(it);
    }
    dec(it); // it will force the 10000 tasks created above to die...
    object * v = task_get(curr);
    dec(curr);
    show_msg((sstream() << "v: " << unbox(v) << "\n").str().c_str());
    object * vc = task_get(children.back());
    for (object * c : children)
        dec(c);
    lean_assert(unbox(v) == 1010);
    lean_assert(unbox(vc) == 2020);
    std::cout << g_task7_counter << "\n";
}


obj_res mk_foo(unsigned n) {
    object * r = alloc_cnstr(0, 1, 0);
    cnstr_set(r, 0, box(n));
    return r;
}

unsigned foo_val(b_obj_arg v) {
    return unbox(cnstr_get(v, 0));
}

object * mk_list(unsigned n) {
    object * r = box(0);
    for (unsigned i = 0; i < n; i++) {
        object * new_r = alloc_cnstr(1, 2, 0);
        cnstr_set(new_r, 0, box(i));
        cnstr_set(new_r, 1, r);
        r = new_r;
    }
    return r;
}

bool contains_borrow(object * l, object * v) {
    if (is_scalar(l)) {
        return false;
    } else {
        object * h = cnstr_get(l, 0);
        object * t = cnstr_get(l, 1);
        if (h == v) {
            return true;
        } else {
            return contains_borrow(t, v);
        }
    }
}

bool contains(object * l, object * v) {
    if (is_scalar(l)) {
        dec(v);
        return false;
    } else {
        object * h = cnstr_get(l, 0);
        object * t = cnstr_get(l, 1);
        if (!is_shared(l)) {
            lean_free_object(l);
        } else {
            inc(h);
            inc(t);
            dec_ref(l);
        }
        if (h == v) {
            dec(h); dec(v); dec(t);
            return true;
        } else {
            dec(h);
            return contains(t, v);
        }
    }
}

inline object * mark_borrowed(object * o) {
    if (is_scalar(o))
        return o;
    else
        return reinterpret_cast<object*>(reinterpret_cast<uintptr_t>(o) | 0x2);
}

inline bool is_borrowed(object * o) {
    return !is_scalar(o) && (reinterpret_cast<uintptr_t>(o) & 0x2) != 0;
}

inline object * get_object(object * o) {
    if (is_scalar(o))
        return o;
    else
        return reinterpret_cast<object*>((reinterpret_cast<uintptr_t>(o) >> 2) << 2);
}

bool contains_hybrid(object * l, object * v) {
    bool l_b       = is_borrowed(l);
    object * l_obj = get_object(l);
    bool v_b       = is_borrowed(v);
    object * v_obj = get_object(v);
    if (is_scalar(l_obj)) {
        if (!v_b) dec(v_obj);
        return false;
    } else {
        object * h_obj = cnstr_get(l_obj, 0);
        object * t_obj = cnstr_get(l_obj, 1);
        object * t;
        if (l_b) {
            t = mark_borrowed(t_obj);
        } else if (!is_shared(l_obj)) {
            lean_free_object(l_obj);
            t = t_obj;
        } else {
            inc(h_obj);
            inc(t_obj);
            dec_ref(l_obj);
            t = mark_borrowed(t_obj);
        }
        if (v_obj == h_obj) {
            if (!l_b) dec(h_obj);
            if (!l_b) dec(t_obj);
            if (!v_b) dec(v_obj);
            return false;
        } else {
            if (!l_b) dec(h_obj);
            return contains_hybrid(t, v);
        }
    }
}

bool contains_fast_hybrid(object * l, object * v) {
    if (is_scalar(l)) {
        dec(v);
        return false;
    } else {
        object * h  = cnstr_get(l, 0);
        object * t  = cnstr_get(l, 1);
        bool shared = is_shared(l);
        if (!shared) {
            lean_free_object(l);
        } else {
            inc(h);
            inc(t);
            dec_ref(l);
        }
        if (h == v) {
            dec(h); dec(v); dec(t);
            return true;
        } else if (!shared) {
            dec(h);
            return contains_fast_hybrid(t, v);
        } else {
            dec(h);
            bool r = contains_borrow(t, v);
            dec(t);
            dec(v);
            return r;
        }
    }
}

void tst17(unsigned n, unsigned sz) {
    {
        timeit timer(std::cout, "contains standard");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            inc(l);
            contains(l, box(sz));
            inc(l);
            contains(l, box(sz/2));
        }
        dec(l);
    }
    {
        timeit timer(std::cout, "contains borrowed");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            contains_borrow(l, box(sz));
            contains_borrow(l, box(sz/2));
        }
        dec(l);
    }
    {
        timeit timer(std::cout, "contains hybrid");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            inc(l);
            contains_hybrid(l, box(sz));
            inc(l);
            contains_hybrid(l, box(sz/2));
        }
        dec(l);
    }
    {
        timeit timer(std::cout, "contains fast hybrid");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            inc(l);
            contains_fast_hybrid(l, box(sz));
            inc(l);
            contains_fast_hybrid(l, box(sz/2));
        }
        dec(l);
    }
}

inline object * get(object * o, unsigned idx) {
    object * r = cnstr_get(o, idx);
    inc(r);
    return r;
}

object * map_add1(object * l) {
    if (is_scalar(l)) {
        return l;
    } else {
        object * h     = cnstr_get(l, 0); inc(h);
        object * t     = cnstr_get(l, 1); inc(t);
        dec(l);
        object * new_h = box(unbox(h)+1);
        object * new_t = map_add1(t);
        object * r     = alloc_cnstr(1, 2, 0);
        cnstr_set(r, 0, new_h);
        cnstr_set(r, 1, new_t);
        return r;
    }
}

object * map_add1_reuse(object * l) {
    if (is_scalar(l)) {
        return l;
    } else {
        object * h = cnstr_get(l, 0); inc(h);
        object * t = cnstr_get(l, 1); inc(t);
        object * r;
        if (is_shared(l)) {
            dec(l);
            r = alloc_cnstr(1, 2, 0);
        } else {
            r = l;
            dec(h);
            dec(t);
        }
        cnstr_set(r, 0, box(0));
        cnstr_set(r, 1, box(0));
        object * new_h = box(unbox(h)+1);
        object * new_t = map_add1_reuse(t);
        cnstr_set(r, 0, new_h);
        cnstr_set(r, 1, new_t);
        return r;
    }
}

object * map_add1_reuse_opt(object * l) {
    if (is_scalar(l)) {
        return l;
    } else {
        object * h = cnstr_get(l, 0);
        object * t = cnstr_get(l, 1);
        object * r;
        if (is_shared(l)) {
            inc(h);
            inc(t);
            dec(l);
            r = alloc_cnstr(1, 2, 0);
        } else {
            r = l;
        }
        object * new_h = box(unbox(h)+1);
        object * new_t = map_add1_reuse_opt(t);
        cnstr_set(r, 0, new_h);
        cnstr_set(r, 1, new_t);
        return r;
    }
}

void tst18(unsigned n, unsigned sz) {
    {
        timeit timer(std::cout, "map");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            lean_assert(!is_shared(l));
            l = map_add1(l);
        }
        dec(l);
    }
    {
        timeit timer(std::cout, "map_reuse");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            lean_assert(!is_shared(l));
            l = map_add1_reuse(l);
        }
        dec(l);
    }
    {
        timeit timer(std::cout, "map_opt");
        object * l = mk_list(sz);
        for (unsigned i = 0; i < n; i++) {
            lean_assert(!is_shared(l));
            l = map_add1_reuse_opt(l);
        }
        dec(l);
    }
}

void tst19() {
    object * s1 = mk_string("hello");
    object * s2 = mk_string("world");
    inc_ref(s1);
    object * s4 = string_append(s1, s2);
    lean_assert(string_eq(s4, "helloworld"));
    lean_assert(string_eq(s1, "hello"));
    dec_ref(s4);
    object * s5 = string_append(s1, s2);
    lean_assert(string_eq(s5, "helloworld"));
    object * b  = mk_string("!");
    object * s6 = string_append(s5, b);
    lean_assert(string_eq(s6, "helloworld!"));
    lean_assert(s5 == s6);
    inc_ref(s6);
    object * s7 = string_push(s6, '!');
    lean_assert(string_eq(s6, "helloworld!"));
    lean_assert(string_eq(s7, "helloworld!!"));
    object * s8 = string_push(s7, 'a');
    lean_assert(string_eq(s8, "helloworld!!a"));
    lean_assert(s7 == s8);
    dec_ref(s2); dec_ref(s6); dec_ref(b); dec_ref(s8);
}

void tst20() {
    lean_assert(nat(LEAN_MAX_SMALL_NAT+1) == nat(LEAN_MAX_SMALL_NAT) + nat(1));
    lean_assert(!nat(LEAN_MAX_SMALL_NAT+1).is_small());
    lean_assert(nat(LEAN_MAX_SMALL_NAT).is_small());
    lean_assert(nat(2) + nat(3) == nat(5));
    lean_assert(!(nat(LEAN_MAX_SMALL_NAT) * nat(LEAN_MAX_SMALL_NAT)).is_small());
    nat tmp = (nat(LEAN_MAX_SMALL_NAT) * nat(LEAN_MAX_SMALL_NAT))/nat(LEAN_MAX_SMALL_NAT);
    lean_assert(tmp.is_small());
    lean_assert(tmp == LEAN_MAX_SMALL_NAT);
    lean_assert(nat(LEAN_MAX_SMALL_NAT) * nat(LEAN_MAX_SMALL_NAT) > nat(LEAN_MAX_SMALL_NAT));
}

void tst21() {
    array_ref<nat> a({nat(1), nat(2), nat(3)});
    lean_assert(a.size() == 3);
    lean_assert(a[0] == nat(1));
    for (nat const & v : a) {
        std::cout << v << "\n";
    }
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    // tst17(40000, 3000);
    tst17(400, 30);
    // tst18(4000, 3000);
    tst18(400, 30);
    tst19();
    tst20();
    tst21();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
