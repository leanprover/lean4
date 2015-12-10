/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/io_state_stream.h"
#include "library/blast/action_result.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
void trace_curr_state();
void trace_target();
void trace_search(char const * msg);
void trace_depth_nchoices();
void trace_action(char const * a);
void trace_curr_state_if(action_result r);

#define lean_trace_action(Code) lean_trace(name({"blast", "action"}), Code)
#define lean_trace_search(Code) lean_trace(name({"blast", "search"}), Code)
#define lean_trace_deadend(Code) lean_trace(name({"blast", "deadend"}), Code)

/** \brief Helper class for pretty printing blast expressions.
    It uses state::to_kernel_expr to export a blast expression
    into an expression that can be processed by the pretty printer */
struct ppb {
    expr m_expr;
    explicit ppb(expr const & e):m_expr(e) {}
};

io_state_stream const & operator<<(io_state_stream const & out, ppb const & e);
io_state_stream const & operator<<(io_state_stream const & out, hypothesis const & h);
}}
