/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/sexpr/option_declarations.h"
#include "library/trace.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/backward/backward_lemmas.h"

#ifndef LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH
#define LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH 8
#endif

namespace lean {
static name * g_backward_chaining_max_depth = nullptr;

unsigned get_backward_chaining_max_depth(options const & o) {
    return o.get_unsigned(*g_backward_chaining_max_depth, LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH);
}

#define lean_back_trace(code) lean_trace(name({"tactic", "back_chaining"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); code)

struct back_chaining_fn {
    tactic_state         m_initial_state;
    type_context_old         m_ctx;
    bool                 m_use_instances;
    unsigned             m_max_depth;
    vm_obj               m_pre_tactic;
    vm_obj               m_leaf_tactic;
    backward_lemma_index m_lemmas;

    struct choice {
        tactic_state         m_state;
        list<backward_lemma> m_lemmas;
        choice(tactic_state const & s, list<backward_lemma> const & lemmas):
            m_state(s), m_lemmas(lemmas) {}
    };

    tactic_state        m_state;
    buffer<choice>      m_choices;

    back_chaining_fn(tactic_state const & s, transparency_mode md, bool use_instances,
                     unsigned max_depth, vm_obj const & pre_tactic, vm_obj const & leaf_tactic,
                     backward_lemma_index const & lemmas):
        m_initial_state(s),
        m_ctx(mk_type_context_for(s, md)),
        m_use_instances(use_instances),
        m_max_depth(max_depth),
        m_pre_tactic(pre_tactic),
        m_leaf_tactic(leaf_tactic),
        m_lemmas(lemmas),
        m_state(m_initial_state) {
        lean_assert(s.goals());
    }

    vm_obj invoke_tactic(vm_obj const & tac) {
        lean_assert(m_state.goals());
        tactic_state tmp = set_goals(m_state, to_list(head(m_state.goals())));
        vm_obj s = to_obj(tmp);
        return invoke(tac, 1, &s);
    }

    lbool invoke_pre_tactic() {
        vm_obj r = invoke_tactic(m_pre_tactic);
        if (optional<tactic_state> new_s = tactic::is_success(r)) {
            if (new_s->goals()) {
                return l_undef;
            } else {
                lean_back_trace(tout() << "pre tactic solved goal\n";);
                m_state = set_goals(*new_s, tail(m_state.goals()));
                return l_true;
            }
        } else {
            lean_back_trace(tout() << "pre tactic rejected goal\n";);
            return l_false;
        }
    }

    bool invoke_leaf_tactic() {
        vm_obj r = invoke_tactic(m_leaf_tactic);
        if (optional<tactic_state> new_s = tactic::is_success(r)) {
            m_state = set_goals(*new_s, tail(m_state.goals()));
            return true;
        } else {
            return false;
        }
    }

    bool try_lemmas(list<backward_lemma> const & lemmas) {
        m_ctx.set_mctx(m_state.mctx());
        list<backward_lemma> it = lemmas;
        while (it) {
            backward_lemma const & blemma = head(it);
            expr lemma = blemma.to_expr(m_ctx);
            lean_back_trace(tout() << "[" << m_choices.size() << "] trying lemma " << lemma << "\n";);
            if (optional<tactic_state> new_state = apply(m_ctx, false, m_use_instances, lemma, m_state)) {
                lean_back_trace(tout() << "succeed\n";);
                if (tail(it)) {
                    m_choices.emplace_back(m_state, tail(it));
                }
                m_state = *new_state;
                return true;
            }
            it = tail(it);
        }
        return false;
    }

    bool backtrack() {
        while (!m_choices.empty()) {
            lean_back_trace(tout() << "[" << m_choices.size() << "] backtracking\n";);
            list<backward_lemma> lemmas = m_choices.back().m_lemmas;
            m_state = m_choices.back().m_state;
            m_choices.pop_back();
            if (try_lemmas(lemmas)) {
                return true;
            }
        }
        return false;
    }

    bool run() {
        while (true) {
          loop_entry:
            lean_back_trace(tout() << "current state:\n" << m_state.pp_core() << "\n";);
            if (!m_state.goals())
                return true;
            if (m_choices.size() >= m_max_depth) {
                lean_back_trace(tout() << "maximum depth reached\n" << m_state.pp_core() << "\n";);
                if (!backtrack())
                    return false;
                goto loop_entry;
            }
            switch (invoke_pre_tactic()) {
            case l_undef:
                break;
            case l_true:
                goto loop_entry;
            case l_false:
                if (!backtrack())
                    return false;
                goto loop_entry;
            }
            metavar_decl g = *m_state.get_main_goal_decl();
            expr target    = m_ctx.whnf(g.get_type());
            list<backward_lemma> lemmas = m_lemmas.find(head_index(target));
            if (!lemmas || !try_lemmas(lemmas)) {
                if (!invoke_leaf_tactic()) {
                    if (!backtrack())
                        return false;
                    goto loop_entry;
                }
            }
        }
    }

    vm_obj operator()() {
        list<expr> goals = m_initial_state.goals();
        m_state = set_goals(m_initial_state, to_list(head(goals)));
        if (run()) {
            tactic_state final_state = set_goals(m_state, tail(goals));
            return tactic::mk_success(final_state);
        } else {
            return tactic::mk_exception("back_chaining failed, use command 'set_option trace.tactic.back_chaining true' to obtain more details", m_initial_state);
        }
    }
};

vm_obj back_chaining(transparency_mode md, bool use_instances, unsigned max_depth,
                     vm_obj const & pre_tactic, vm_obj const & leaf_tactic, backward_lemma_index const & lemmas, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    return back_chaining_fn(s, md, use_instances, max_depth, pre_tactic, leaf_tactic, lemmas)();
}

vm_obj tactic_backward_chaining(vm_obj const & md, vm_obj const & use_instances, vm_obj const & max_depth,
                                vm_obj const & pre_tactics, vm_obj const & leaf_tactic,
                                vm_obj const & lemmas, vm_obj const & s) {
    return back_chaining(to_transparency_mode(md), to_bool(use_instances),
                         force_to_unsigned(max_depth),
                         pre_tactics, leaf_tactic, to_backward_lemmas(lemmas), tactic::to_state(s));
}

void initialize_backward_chaining() {
    DECLARE_VM_BUILTIN(name({"tactic", "backward_chaining_core"}),   tactic_backward_chaining);
    register_trace_class(name({"tactic", "back_chaining"}));
    g_backward_chaining_max_depth = new name{"back_chaining", "max_depth"};
    register_unsigned_option(*g_backward_chaining_max_depth, LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH,
                             "maximum number of nested backward chaining steps");
}

void finalize_backward_chaining() {
    delete g_backward_chaining_max_depth;
}
}
