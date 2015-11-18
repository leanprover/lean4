/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/choice_point.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
LEAN_THREAD_VALUE(bool, g_trace, false);

bool is_trace_enabled() {
    return g_trace;
}

void trace_curre_state() {
    if (g_trace) {
        auto out = diagnostic(env(), ios());
        out << "state [" << curr_state().get_proof_depth() << "], #choice: " << get_num_choice_points() << "\n";
        display_curr_state();
    }
}

void trace(char const * msg) {
    if (g_trace) {
        ios().get_diagnostic_channel() << msg << "\n\n";
    }
}

void trace_action(char const * a) {
    if (g_trace) {
        ios().get_diagnostic_channel() << "== action: " << a << " ==>\n\n";
    }
}

void trace_curre_state_if(action_result r) {
    if (g_trace && !failed(r))
        trace_curre_state();
}

scope_trace::scope_trace(bool enable):
    m_old(g_trace) {
    g_trace = enable;
}

scope_trace::scope_trace(options const & o):
    scope_trace(get_blast_trace(o)) {
}

scope_trace::~scope_trace() {
    g_trace = m_old;
}
}}
