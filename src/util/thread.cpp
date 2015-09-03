/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
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

typedef std::vector<std::pair<thread_finalizer, void*>> thread_finalizers;

void run_thread_finalizers_core(thread_finalizers & fns) {
    unsigned i = fns.size();
    while (i > 0) {
        --i;
        auto fn = fns[i].first;
        fn(fns[i].second);
    }
    fns.clear();
}

// We have two different implementations of the following procedures.
//
//   void register_thread_finalizer(thread_finalizer fn, void * p);
//   void register_post_thread_finalizer(thread_finalizer fn, void * p);
//   void run_thread_finalizers();
//
// The implementation is selected by using the LEAN_AUTO_THREAD_FINALIZATION compilation directive.
// We can remove the implementation based on pthreads after the new thread_local C++11 keyword is properly
// implemented in all platforms.
// In the meantime, when LEAN_AUTO_THREAD_FINALIZATION is defined/set, we use a thread finalization
// procedure based on the pthread API.
// Remark: we only need this feature when Lean is being used as a library.
// Example: the C API is being used from Haskell, and the execution threads
// are being created by Haskell.
// Remark: for the threads created by Lean, we explicitly create the thread finalizers.
// The idea is to avoid memory leaks even when LEAN_AUTO_THREAD_FINALIZATION is not used.

#if defined(LEAN_AUTO_THREAD_FINALIZATION)
// pthread based implementation

typedef std::pair<thread_finalizers, thread_finalizers> thread_finalizers_pair;

class thread_finalizers_manager {
    pthread_key_t g_key;
public:
    thread_finalizers_manager() {
        pthread_key_create(&g_key, finalize_thread);
        init_thread(); // initialize main thread
    }

    ~thread_finalizers_manager() {
        finalize_thread(get_pair()); // finalize main thread
        pthread_key_delete(g_key);
    }

    thread_finalizers_pair * get_pair() {
        return reinterpret_cast<thread_finalizers_pair*>(pthread_getspecific(g_key));
    }

    void init_thread() {
        if (get_pair() == nullptr) {
            thread_finalizers_pair * p = new thread_finalizers_pair();
            pthread_setspecific(g_key, p);
        }
    }

    thread_finalizers & get_thread_finalizers() {
        init_thread();
        return get_pair()->first;
    }

    thread_finalizers & get_post_thread_finalizers() {
        init_thread();
        return get_pair()->second;
    }

    static void finalize_thread(void * d) {
        if (d) {
            thread_finalizers_pair * p = reinterpret_cast<thread_finalizers_pair*>(d);
            run_thread_finalizers_core(p->first);
            run_thread_finalizers_core(p->second);
            delete p;
        }
    }
};

thread_finalizers_manager * g_aux = nullptr;

thread_finalizers_manager & get_manager() {
    if (!g_aux)
        g_aux = new thread_finalizers_manager();
    return *g_aux;
}

void delete_thread_finalizer_manager() {
    delete g_aux;
}

void register_thread_finalizer(thread_finalizer fn, void * p) {
    get_manager().get_thread_finalizers().emplace_back(fn, p);
}

void register_post_thread_finalizer(thread_finalizer fn, void * p) {
    get_manager().get_post_thread_finalizers().emplace_back(fn, p);
}

void run_thread_finalizers() {
}

void run_post_thread_finalizers() {
}
#else
// reference implementation
LEAN_THREAD_PTR(thread_finalizers, g_finalizers);
LEAN_THREAD_PTR(thread_finalizers, g_post_finalizers);

void delete_thread_finalizer_manager() {}

void register_thread_finalizer(thread_finalizer fn, void * p) {
    if (!g_finalizers)
        g_finalizers = new thread_finalizers();
    g_finalizers->emplace_back(fn, p);
}

void register_post_thread_finalizer(thread_finalizer fn, void * p) {
    if (!g_post_finalizers)
        g_post_finalizers = new thread_finalizers();
    g_post_finalizers->emplace_back(fn, p);
}

void run_thread_finalizers(thread_finalizers * fns) {
    if (fns) {
        run_thread_finalizers_core(*fns);
        delete fns;
    }
}

void run_thread_finalizers() {
    run_thread_finalizers(g_finalizers);
    g_finalizers      = nullptr;
}

void run_post_thread_finalizers() {
    run_thread_finalizers(g_post_finalizers);
    g_post_finalizers = nullptr;
}
#endif
}
