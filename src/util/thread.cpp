/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
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
}
