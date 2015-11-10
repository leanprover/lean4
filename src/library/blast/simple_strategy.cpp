/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/assumption.h"
#include "library/blast/intros.h"

namespace lean {
namespace blast {
/** \brief Implement a simple proof strategy for blast.
    We use it mainly for testing new actions and the whole blast infra-structure. */
class simple_strategy {
    unsigned                   m_max_depth;
    unsigned                   m_init_depth;
    unsigned                   m_inc_depth;

    enum status { NoAction, ClosedBranch, Continue };

    optional<unsigned> activate_hypothesis() {
        return curr_state().activate_hypothesis();
    }

    pair<status, expr> next_action() {
        if (intros_action()) {
            return mk_pair(Continue, expr());
        } else if (activate_hypothesis()) {
            // TODO(Leo): we should probably eagerly simplify the activated hypothesis.
            return mk_pair(Continue, expr());
        } else if (auto pr = assumption_action()) {
            return mk_pair(ClosedBranch, *pr);
        } else {
            // TODO(Leo): add more actions...
            return mk_pair(NoAction, expr());
        }
    }

    optional<expr> resolve(expr pr) {
        while (curr_state().has_proof_steps()) {
            proof_step s = curr_state().top_proof_step();
            if (auto new_pr = s.resolve(curr_state(), pr)) {
                pr = *new_pr;
                curr_state().pop_proof_step();
            } else {
                return none_expr(); // continue the search
            }
        }
        return some_expr(pr); // closed all branches
    }

    optional<expr> search_upto(unsigned depth) {
        while (true) {
            if (curr_state().get_proof_depth() > depth) {
                // maximum depth reached
                if (!next_choice_point()) {
                    return none_expr();
                }
            }
            auto s = next_action();
            switch (s.first) {
            case NoAction:
                if (!next_choice_point())
                    return none_expr();
                break;
            case ClosedBranch:
                if (auto pr = resolve(s.second))
                    return pr;
                break;
            case Continue:
                break;
            }
        }
    }

    optional<expr> search() {
        state s    = curr_state();
        unsigned d = m_init_depth;
        while (d <= m_max_depth) {
            if (auto r = search_upto(d))
                return r;
            d += m_inc_depth;
            curr_state() = s;
            clear_choice_points();
        }
        return none_expr();
    }

public:
    simple_strategy() {
        options o = ios().get_options();
        m_max_depth  = get_blast_max_depth(o);
        m_init_depth = get_blast_init_depth(o);
        m_inc_depth  = get_blast_inc_depth(o);
    }

    optional<expr> operator()() {
        return search();
    }
};

optional<expr> apply_simple_strategy() {
    return simple_strategy()();
}
}}
