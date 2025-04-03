/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Henrik Böving
*/
#include <lean/lean.h>
#include "runtime/mutex.h"
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/thread.h"

namespace lean {

static lean_external_class * g_basemutex_external_class = nullptr;
static void basemutex_finalizer(void * h) {
    delete static_cast<mutex *>(h);
}
static void basemutex_foreach(void *, b_obj_arg) {}

static mutex * basemutex_get(lean_object * mtx) {
    return static_cast<mutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_new(obj_arg) {
    return io_result_mk_ok(lean_alloc_external(g_basemutex_external_class, new mutex));
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_lock(b_obj_arg mtx, obj_arg) {
    basemutex_get(mtx)->lock();
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_try_lock(b_obj_arg mtx, obj_arg) {
    bool success = basemutex_get(mtx)->try_lock();
    return io_result_mk_ok(box(success));
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_unlock(b_obj_arg mtx, obj_arg) {
    basemutex_get(mtx)->unlock();
    return io_result_mk_ok(box(0));
}

static lean_external_class * g_condvar_external_class = nullptr;
static void condvar_finalizer(void * h) {
    delete static_cast<condition_variable *>(h);
}
static void condvar_foreach(void *, b_obj_arg) {}

static condition_variable * condvar_get(lean_object * mtx) {
    return static_cast<condition_variable *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_new(obj_arg) {
    return io_result_mk_ok(lean_alloc_external(g_condvar_external_class, new condition_variable));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_wait(b_obj_arg condvar, b_obj_arg mtx, obj_arg) {
    unique_lock<mutex> lock(*basemutex_get(mtx), std::adopt_lock_t());
    condvar_get(condvar)->wait(lock);
    lock.release();
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_one(b_obj_arg condvar, obj_arg) {
    condvar_get(condvar)->notify_one();
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_all(b_obj_arg condvar, obj_arg) {
    condvar_get(condvar)->notify_all();
    return io_result_mk_ok(box(0));
}

static lean_external_class * g_baserecmutex_external_class = nullptr;
static void baserecmutex_finalizer(void * h) {
    delete static_cast<recursive_mutex *>(h);
}
static void baserecmutex_foreach(void *, b_obj_arg) {}

static recursive_mutex * baserecmutex_get(lean_object * mtx) {
    return static_cast<recursive_mutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_new(obj_arg) {
    return io_result_mk_ok(lean_alloc_external(g_baserecmutex_external_class, new recursive_mutex));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_lock(b_obj_arg mtx, obj_arg) {
    baserecmutex_get(mtx)->lock();
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_try_lock(b_obj_arg mtx, obj_arg) {
    bool success = baserecmutex_get(mtx)->try_lock();
    return io_result_mk_ok(box(success));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_unlock(b_obj_arg mtx, obj_arg) {
    baserecmutex_get(mtx)->unlock();
    return io_result_mk_ok(box(0));
}

void initialize_mutex() {
    g_basemutex_external_class = lean_register_external_class(basemutex_finalizer, basemutex_foreach);
    g_condvar_external_class = lean_register_external_class(condvar_finalizer, condvar_foreach);
    g_baserecmutex_external_class = lean_register_external_class(baserecmutex_finalizer, baserecmutex_foreach);
}

void finalize_mutex() {
}

}
