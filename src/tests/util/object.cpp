/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "runtime/serializer.h"
#include "util/object_ref.h"
#include "util/init_module.h"
using namespace lean;

#define USED(x) (void)(x)

object * f(object *) {
    std::cout << "executing f...\n";
    return box(10);
}

static void tst1() {
    object_ref t(mk_thunk(alloc_closure(f, 1, 0)));
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

static void tst2() {
    object * c = alloc_closure(g, 1, 0);
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
static void tst3() {
    object_ref t(mk_thunk(alloc_closure(h, 1, 0)));
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

static void tst4() {
    object_ref t(mk_thunk(alloc_closure(r, 1, 0)));
    object * r3  = thunk_get(t.raw());
    object * r4  = thunk_get(t.raw());
    lean_assert(string_eq(r3, "hello world"));
    lean_assert(string_eq(r4, "hello world"));
    USED(r3); USED(r4);
}

static void tst5() {
    object_ref t(mk_thunk(alloc_closure(r, 1, 0)));
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
    lean_assert(strcmp(string_data(str), "hello world") == 0);
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
    object * c     = alloc_closure(reinterpret_cast<lean_cfun>(task3_fn), 2, 1);
    closure_set_arg(c, 0, val);
    return task_start(c);
}

obj_res mk_task2(b_obj_arg task1) {
    inc(task1);
    return task_map(alloc_closure(add_10, 1, 0), task1);
 }

obj_res mk_task3(b_obj_arg task1) {
    inc_ref(task1);
    return task_bind(task1, alloc_closure(mk_task3_fn, 1, 0));
}

static void tst6() {
    scoped_task_manager m(8);
    object_ref task1(task_start(alloc_closure(task1_fn, 1, 0)));
    object_ref task2(mk_task2(task1.raw()));
    object_ref task3(mk_task3(task1.raw()));
    object * r1 = task_get(task2.raw());
    object * r2 = task_get(task3.raw());
    std::cout << "r1: " << unbox(r1) << "\n";
    std::cout << "r2: " << unbox(r2) << "\n";
    lean_assert(unbox(r1) == 20);
    lean_assert(unbox(r2) == 110);
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
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
