/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/trace.h"
#include "library/io_state_stream.h"
#include "library/blast/blast.h"
#include "library/blast/choice_point.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
MK_THREAD_LOCAL_GET_DEF(expr, get_last_target);

void trace_target() {
    if (lean_is_trace_enabled(name({"blast", "search"})) &&
        curr_state().get_target() != get_last_target()) {
        lean_trace_search(tout() << "target " << ppb(curr_state().get_target()) << "\n";);
        get_last_target() = curr_state().get_target();
    }
}

MK_THREAD_LOCAL_GET_DEF(std::string, get_state_str);

void trace_curr_state() {
    if (lean_is_trace_enabled(name({"blast", "state"}))) {
        std::shared_ptr<output_channel> out(new string_output_channel());
        io_state tmp(ios(), out, out);
        io_state_stream strm(env(), tmp);
        curr_state().display(strm);
        std::string new_str = static_cast<string_output_channel*>(out.get())->str();
        if (get_state_str() == new_str)
            return;
        unsigned i = 0;
        unsigned sz1 = get_state_str().size();
        unsigned sz2 = new_str.size();
        while (i < sz1 && i < sz2 && get_state_str()[i] == new_str[i]) {
            i++;
        }
        if (i == 0) {
            lean_trace(name({"blast", "state"}), tout() << "\n" << new_str;);
        } else {
            // consume trailing ,
            if (i + 1 < sz2 && new_str[i] == ',' && new_str[i+1] == '\n')
                i += 2;
            // move to beginning of the line
            while (i > 0 && new_str[i-1] != '\n')
                i--;
            lean_trace(name({"blast", "state"}), tout() << "\n...\n" << new_str.substr(i););
        }
        get_state_str() = new_str;
    }
}

typedef pair<unsigned, unsigned> unsigned_pair;
MK_THREAD_LOCAL_GET(unsigned_pair, get_depth_num_choices, mk_pair(-1, -1));

void trace_depth_nchoices() {
    if (!lean_is_trace_enabled(name({"blast", "search"})))
        return;
    auto & p = get_depth_num_choices();
    if (p.first == curr_state().get_proof_depth() &&
        p.second == get_num_choice_points())
        return;
    p = mk_pair(curr_state().get_proof_depth(), get_num_choice_points());
    lean_trace_search(tout() << "depth: " << p.first << ", #choices: " << p.second << "\n";);
}

void trace_search(char const * msg) {
    lean_trace_search(tout() << msg << "\n";);
}

void trace_action(char const * a) {
    lean_trace_action(tout() << a << "\n";);
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

io_state_stream const & operator<<(io_state_stream const & out, hypothesis const & h) {
    out << ppb(h.get_self());
    return out;
}
}}
