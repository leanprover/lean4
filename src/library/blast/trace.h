/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/action_result.h"
#include "library/io_state_stream.h"

namespace lean {
namespace blast {
void trace_curr_state();
void trace(char const * msg);
void trace_action(char const * a);
void trace_curr_state_if(action_result r);
bool is_trace_enabled();

class scope_trace {
    bool m_old;
public:
    scope_trace();
    scope_trace(bool enable);
    ~scope_trace();
};

/** \brief Helper class for pretty printing blast expressions.
    It uses state::to_kernel_expr to export a blast expression
    into an expression that can be processed by the pretty printer */
struct ppb {
    expr m_expr;
    explicit ppb(expr const & e):m_expr(e) {}
};

io_state_stream const & operator<<(io_state_stream const & out, ppb const & e);
}}
