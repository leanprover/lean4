/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <pthread.h>
#include <vector>
#include <iostream>
#include "util/thread.h"

namespace lean {
#if defined(LEAN_USE_BOOST)
static boost::thread::attributes * g_thread_attributes = nullptr;
void initialize_thread() {
    g_thread_attributes = new boost::thread::attributes();
    g_thread_attributes->set_stack_size(8192*1024); // 8Mb
}
void finalize_thread() {
    delete g_thread_attributes;
}
void set_thread_stack_size(size_t sz) {
    g_thread_attributes->set_stack_size(sz);
}
boost::thread::attributes const & get_thread_attributes() {
    return *g_thread_attributes;
}
#else
void initialize_thread() {}
void finalize_thread() {}
#endif

typedef std::vector<thread_finalizer> thread_finalizers;
LEAN_THREAD_PTR(thread_finalizers, g_finalizers);
LEAN_THREAD_PTR(thread_finalizers, g_post_finalizers);

void run_thread_finalizers(thread_finalizers * fns) {
    if (fns) {
        unsigned i = fns->size();
        while (i > 0) {
            --i;
            auto fn = (*fns)[i];
            fn();
        }
        delete fns;
    }
}

void run_thread_finalizers() {
    run_thread_finalizers(g_finalizers);
    g_finalizers = nullptr;
}

void run_post_thread_finalizers() {
    run_thread_finalizers(g_post_finalizers);
    g_post_finalizers = nullptr;
}

#if defined(LEAN_AUTO_THREAD_FINALIZATION)
// This is an auxiliary class used to finalize thread local storage.
// It can be removed after the new thread_local C++11 keyword is properly
// implemented in all platforms.
// In the meantime, we create a "fake" key that is only used to trigger
// the Lean thread finalization procedures.
// We only need this feature when Lean is being used as a library.
// Example: the C API is being used from Haskell, and the execution threads
// are being created by Haskell.
// Remark: for the threads created by Lean, we explicitly create the thread finalizers.
// The idea is to avoid memory leaks even when LEAN_AUTO_THREAD_FINALIZATION is not used.
class thread_key_init {
    pthread_key_t g_key;
public:
    static void finalize_thread(void *) { // NOLINT
        run_thread_finalizers();
        run_post_thread_finalizers();
    }

    thread_key_init() {
        pthread_key_create(&g_key, finalize_thread);
    }

    ~thread_key_init() {
        pthread_key_delete(g_key);
    }

    void init_thread() {
        void * p;
        if ((p = pthread_getspecific(g_key)) == nullptr) {
            pthread_setspecific(g_key, reinterpret_cast<void*>(1));
        }
    }
};

static thread_key_init g_aux;
#endif

void register_thread_finalizer(thread_finalizer fn) {
    if (!g_finalizers) {
        g_finalizers = new thread_finalizers();
        #if defined(LEAN_AUTO_THREAD_FINALIZATION)
        g_aux.init_thread();
        #endif
    }
    g_finalizers->push_back(fn);
}

void register_post_thread_finalizer(thread_finalizer fn) {
    if (!g_post_finalizers)
        g_post_finalizers = new thread_finalizers();
    g_post_finalizers->push_back(fn);
}
}
