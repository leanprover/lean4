/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/io_state_stream.h"
#include "library/blast/blast.h"
#include "library/blast/choice_point.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
void trace_curr_state() {
    lean_trace(name({"blast", "state"}), tout() << "\n"; curr_state().display(tout()););
}

void trace_search(char const * msg) {
    lean_trace(name({"blast", "search"}), tout() << msg << "\n";);
}

void trace_action(char const * a) {
    lean_trace(name({"blast", "action"}), tout() << a << "\n";);
}

void trace_curr_state_if(action_result r) {
    if (!failed(r) && !solved(r))
        trace_curr_state();
}

io_state_stream const & operator<<(io_state_stream const & out, ppb const & e) {
    expr tmp = curr_state().to_kernel_expr(e.m_expr);
    out << tmp;
    return out;
}
}}
