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

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_new() {
    return lean_alloc_external(g_basemutex_external_class, new mutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_lock(b_obj_arg mtx) {
    basemutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basemutex_try_lock(b_obj_arg mtx) {
    bool success = basemutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_unlock(b_obj_arg mtx) {
    basemutex_get(mtx)->unlock();
    return box(0);
}

static lean_external_class * g_condvar_external_class = nullptr;
static void condvar_finalizer(void * h) {
    delete static_cast<condition_variable *>(h);
}
static void condvar_foreach(void *, b_obj_arg) {}

static condition_variable * condvar_get(lean_object * mtx) {
    return static_cast<condition_variable *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_new() {
    return lean_alloc_external(g_condvar_external_class, new condition_variable);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_wait(b_obj_arg condvar, b_obj_arg mtx) {
    unique_lock<mutex> lock(*basemutex_get(mtx), std::adopt_lock_t());
    condvar_get(condvar)->wait(lock);
    lock.release();
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_one(b_obj_arg condvar) {
    condvar_get(condvar)->notify_one();
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_all(b_obj_arg condvar) {
    condvar_get(condvar)->notify_all();
    return box(0);
}

static lean_external_class * g_baserecmutex_external_class = nullptr;
static void baserecmutex_finalizer(void * h) {
    delete static_cast<recursive_mutex *>(h);
}
static void baserecmutex_foreach(void *, b_obj_arg) {}

static recursive_mutex * baserecmutex_get(lean_object * mtx) {
    return static_cast<recursive_mutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_new() {
    return lean_alloc_external(g_baserecmutex_external_class, new recursive_mutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_lock(b_obj_arg mtx) {
    baserecmutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_baserecmutex_try_lock(b_obj_arg mtx) {
    bool success = baserecmutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_unlock(b_obj_arg mtx) {
    baserecmutex_get(mtx)->unlock();
    return box(0);
}

static lean_external_class * g_basesharedmutex_external_class = nullptr;
static void basesharedmutex_finalizer(void * h) {
    delete static_cast<shared_mutex *>(h);
}
static void basesharedmutex_foreach(void *, b_obj_arg) {}

static shared_mutex * basesharedmutex_get(lean_object * mtx) {
    return static_cast<shared_mutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_new() {
    return lean_alloc_external(g_basesharedmutex_external_class, new shared_mutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_write(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basesharedmutex_try_write(b_obj_arg mtx) {
    bool success = basesharedmutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_unlock_write(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->unlock();
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_read(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->lock_shared();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basesharedmutex_try_read(b_obj_arg mtx) {
    bool success = basesharedmutex_get(mtx)->try_lock_shared();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_unlock_read(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->unlock_shared();
    return box(0);
}

void initialize_mutex() {
    g_basemutex_external_class = lean_register_external_class(basemutex_finalizer, basemutex_foreach);
    g_condvar_external_class = lean_register_external_class(condvar_finalizer, condvar_foreach);
    g_baserecmutex_external_class = lean_register_external_class(baserecmutex_finalizer, baserecmutex_foreach);
    g_basesharedmutex_external_class = lean_register_external_class(basesharedmutex_finalizer, basesharedmutex_foreach);
}

void finalize_mutex() {
}

}
