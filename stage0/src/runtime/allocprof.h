/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/object.h"
namespace lean {
/* Low tech runtime allocation profiler.
   We need to compile Lean using RUNTIME_STATS=ON to use it. */
class allocprof {
    std::ostream & m_out;
    std::string    m_msg;
#ifdef LEAN_RUNTIME_STATS
    uint64 m_num_ctor;
    uint64 m_num_closure;
    uint64 m_num_string;
    uint64 m_num_array;
    uint64 m_num_thunk;
    uint64 m_num_task;
    uint64 m_num_ext;
#endif
public:
    allocprof(std::ostream & out, char const * msg);
    ~allocprof();
};
}
