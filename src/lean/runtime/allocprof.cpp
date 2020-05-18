/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/allocprof.h"
namespace lean {
allocprof::allocprof(std::ostream & out, char const * msg):
    m_out(out), m_msg(msg) {
#ifdef LEAN_RUNTIME_STATS
        m_num_ctor    = g_num_ctor;
        m_num_closure = g_num_closure;
        m_num_string  = g_num_string;
        m_num_array   = g_num_array;
        m_num_thunk   = g_num_thunk;
        m_num_task    = g_num_task;
        m_num_ext     = g_num_ext;
#endif
}
allocprof::~allocprof() {
    m_out << m_msg << "\n";
#ifdef LEAN_RUNTIME_STATS
    uint64 num_ctor    = g_num_ctor - m_num_ctor;
    uint64 num_closure = g_num_closure - m_num_closure;
    uint64 num_string  = g_num_string - m_num_string;
    uint64 num_array   = g_num_array - m_num_array;
    uint64 num_thunk   = g_num_thunk - m_num_thunk;
    uint64 num_task    = g_num_task - m_num_task;
    uint64 num_ext     = g_num_ext - m_num_ext;
    if (num_ctor > 0)    m_out << "num. constructor: " << num_ctor << "\n";
    if (num_closure > 0) m_out << "num. closure:     " << num_closure << "\n";
    if (num_string > 0)  m_out << "num. string:      " << num_string << "\n";
    if (num_array > 0)   m_out << "num. array:       " << num_array << "\n";
    if (num_thunk > 0)   m_out << "num. thunk:       " << num_thunk << "\n";
    if (num_task > 0)    m_out << "num. task:        " << num_task << "\n";
    if (num_ext > 0)     m_out << "num. external:    " << num_ext << "\n";
    if (num_ctor == 0 && num_closure == 0 && num_string == 0 && num_array == 0 &&
        num_thunk == 0 && num_task == 0 && num_ext == 0) {
        m_out << "***no runtime object allocation has occurred**\n";
    }
    m_out << "-------------\n";
#else
    m_out << "Allocation profiling data is not available, compile lean using `-D RUNTIME_STATS=ON`\n";
#endif
}
}
