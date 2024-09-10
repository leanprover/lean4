/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <iostream>
#ifdef LEAN_WINDOWS
#include <windows.h>
# ifdef LEAN_AUTO_THREAD_FINALIZATION
#include <pthread.h>
# endif
#else
#include <pthread.h>
#endif
#include <lean/config.h>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/exception.h"
#include "runtime/alloc.h"
#include "runtime/stack_overflow.h"

#ifndef LEAN_DEFAULT_THREAD_STACK_SIZE
#define LEAN_DEFAULT_THREAD_STACK_SIZE 8*1024*1024 // 8Mb
#endif

namespace lean {
static std::vector<std::function<void()>> * g_thread_local_reset_fns;

static void initialize_thread_local_reset_fns() {
    g_thread_local_reset_fns = new std::vector<std::function<void()>>();
}

static void finalize_thread_local_reset_fns() {
    delete g_thread_local_reset_fns;
}

void register_thread_local_reset_fn(std::function<void()> fn) {
    g_thread_local_reset_fns->push_back(fn);
}

void reset_thread_local() {
    for (std::function<void()> const & fn : *g_thread_local_reset_fns) {
        fn();
    }
}

using runnable = std::function<void()>;

extern "C" LEAN_EXPORT void lean_initialize_thread() {
#ifdef LEAN_SMALL_ALLOCATOR
    init_thread_heap();
#endif
}

extern "C" LEAN_EXPORT void lean_finalize_thread() {
    run_thread_finalizers();
    run_post_thread_finalizers();
}

static void thread_main(void * p) {
    lean_initialize_thread();
    std::unique_ptr<runnable> f;
    f.reset(reinterpret_cast<runnable *>(p));

    (*f)();
    f.reset();

    lean_finalize_thread();
}

#if defined(LEAN_MULTI_THREAD)
size_t lthread::m_thread_stack_size = LEAN_DEFAULT_THREAD_STACK_SIZE;

void lthread::set_thread_stack_size(size_t sz) {
    m_thread_stack_size = sz + LEAN_STACK_BUFFER_SPACE;
}

size_t lthread::get_thread_stack_size() {
    return m_thread_stack_size;
}

static runnable mk_thread_proc(runnable const & p, size_t max) {
    return [=]() { set_max_heartbeat(max); p(); }; // NOLINT
}

#if defined(LEAN_WINDOWS)
/* Windows version */
struct lthread::imp {
    std::function<void(void)> m_proc;
    HANDLE                    m_thread;

    static DWORD WINAPI _main(void * p) {
        thread_main(p);
        return 0;
    }

    imp(runnable const & p) {
        runnable * f = new std::function<void()>(mk_thread_proc(p, get_max_heartbeat()));
        m_thread = CreateThread(nullptr, m_thread_stack_size,
                                _main, f, 0, nullptr);
        if (m_thread == NULL) {
            throw exception("failed to create thread");
        }
    }

    ~imp() {
        CloseHandle(m_thread);
    }

    void join() {
        if (WaitForSingleObject(m_thread, INFINITE) == WAIT_FAILED) {
            throw exception("failed to join thread");
        }
    }
};
#else
/* OSX/Linux version based on pthreads */
struct lthread::imp {
    pthread_attr_t            m_attr;
    pthread_t                 m_thread;
    bool                      m_joined = false;

    static void * _main(void * p) {
        stack_guard guard;
        thread_main(p);
        return nullptr;
    }

    imp(runnable const & p) {
        pthread_attr_init(&m_attr);
        if (pthread_attr_setstacksize(&m_attr, m_thread_stack_size)) {
            throw exception("failed to set thread stack size");
        }
        runnable * f = new std::function<void()>(mk_thread_proc(p, get_max_heartbeat()));
        if (pthread_create(&m_thread, &m_attr, _main, f)) {
            throw exception("failed to create thread");
        }
    }

    ~imp() {
        pthread_attr_destroy(&m_attr);
        if (!m_joined) pthread_detach(m_thread);
    }

    void join() {
        m_joined = true;
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

static thread_finalizers_manager * g_thread_finalizers_mgr = nullptr;

// TODO(gabriel): race condition with thread finalizers
void delete_thread_finalizer_manager() {
    // delete g_thread_finalizers_mgr;
    // g_thread_finalizers_mgr = nullptr;
}

void register_thread_finalizer(thread_finalizer fn, void * p) {
    g_thread_finalizers_mgr->get_thread_finalizers().emplace_back(fn, p);
}

void register_post_thread_finalizer(thread_finalizer fn, void * p) {
    g_thread_finalizers_mgr->get_post_thread_finalizers().emplace_back(fn, p);
}

void run_thread_finalizers() {
    if (auto p = g_thread_finalizers_mgr->get_pair())
        run_thread_finalizers_core(p->first);
}

void run_post_thread_finalizers() {
    if (auto p = g_thread_finalizers_mgr->get_pair())
        run_thread_finalizers_core(p->second);
}

void initialize_thread() {
    g_thread_finalizers_mgr = new thread_finalizers_manager;
    initialize_thread_local_reset_fns();
}
void finalize_thread() {
    finalize_thread_local_reset_fns();
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

void initialize_thread() {
    initialize_thread_local_reset_fns();
}
void finalize_thread() {
    finalize_thread_local_reset_fns();
}
#endif
}
