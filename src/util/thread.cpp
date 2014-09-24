/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
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

void register_thread_finalizer(thread_finalizer fn) {
    if (!g_finalizers)
        g_finalizers = new thread_finalizers();
    g_finalizers->push_back(fn);
}

void register_post_thread_finalizer(thread_finalizer fn) {
    if (!g_post_finalizers)
        g_post_finalizers = new thread_finalizers();
    g_post_finalizers->push_back(fn);
}

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
}

void run_post_thread_finalizers() {
    run_thread_finalizers(g_post_finalizers);
}
}
