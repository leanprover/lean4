/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <pthread.h>
#include <vector>
#include <iostream>
#if defined(LEAN_WINDOWS)
#include <windows.h>
#endif
#include "util/thread.h"
#include "util/exception.h"

#ifndef LEAN_DEFAULT_THREAD_STACK_SIZE
#define LEAN_DEFAULT_THREAD_STACK_SIZE 8*1024*1024 // 8Mb
#endif

namespace lean {
#if defined(LEAN_MULTI_THREAD)
size_t lthread::m_thread_stack_size = LEAN_DEFAULT_THREAD_STACK_SIZE;

void lthread::set_thread_stack_size(size_t sz) {
    m_thread_stack_size = sz + LEAN_STACK_BUFFER_SPACE;
}

size_t lthread::get_thread_stack_size() {
    return m_thread_stack_size;
}

#if defined(LEAN_WINDOWS)
/* Windows version */
struct lthread::imp {
    std::function<void(void)> m_proc;
    HANDLE                    m_thread;

    static DWORD WINAPI _main(void * p) {
        (*reinterpret_cast<std::function<void(void)>*>(p))();
        return 0;
    }

    imp(std::function<void(void)> const & p):
        m_proc(p) {
        m_thread = CreateThread(nullptr, m_thread_stack_size,
                                _main, &m_proc, 0, nullptr);
    }

    void join() {
        WaitForSingleObject(m_thread, INFINITE);
    }
};
#else
/* OSX/Linux version based on pthreads */
struct lthread::imp {
    std::function<void(void)> m_proc;
    pthread_attr_t            m_attr;
    pthread_t                 m_thread;

    static void * _main(void * p) {
        (*reinterpret_cast<std::function<void(void)>*>(p))();
        return nullptr;
    }

    imp(std::function<void(void)> const & p):
        m_proc(p) {
        pthread_attr_init(&m_attr);
        if (pthread_attr_setstacksize(&m_attr, m_thread_stack_size)) {
            throw exception("failed to set thread stack size");
        }
        if (pthread_create(&m_thread, &m_attr, _main, &m_proc)) {
            throw exception("failed to create thread");
        }
    }
    ~imp() {
        pthread_attr_destroy(&m_attr);
    }

    void join() {
        if (pthread_join(m_thread, nullptr)) {
            throw exception("failed to join thread");
        }
    }
};
#endif
lthread::lthread(std::function<void(void)> const & p):m_imp(new imp(p)) {}

lthread::~lthread() {}

void lthread::join() { m_imp->join(); }
#endif

void initialize_thread() {}
void finalize_thread() {}

LEAN_THREAD_VALUE(bool, g_finalizing, false);

bool in_thread_finalization() {
    return g_finalizing;
}

typedef std::vector<std::pair<thread_finalizer, void*>> thread_finalizers;

void run_thread_finalizers_core(thread_finalizers & fns) {
    g_finalizing = true;
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

static thread_finalizers_manager * g_aux = nullptr;

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
