/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/interrupt.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/fun_info.h"
#include "library/idx_metavar.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/hinst_lemmas.h"

namespace lean {
void ematch_state::internalize(type_context & ctx, expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Constant: case expr_kind::Meta:
    case expr_kind::Local:    case expr_kind::Lambda:
    case expr_kind::Let:
        break;
    case expr_kind::Pi:
        if (is_arrow(e) && ctx.is_prop(e)) {
            internalize(ctx, binding_domain(e));
            internalize(ctx, binding_body(e));
        }
        break;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize(ctx, macro_arg(e, i));
        break;
    case expr_kind::App: {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        if ((is_constant(f) && !has_no_inst_pattern_attribute(ctx.env(), const_name(f))) ||
            (is_local(f))) {
            expr_set s;
            if (auto old_s = m_app_map.find(head_index(f)))
                s = *old_s;
            s.insert(e);
            m_app_map.insert(head_index(f), s);
        }
        for (expr const & arg : args) {
            internalize(ctx, arg);
        }
        break;
    }}
}

bool ematch_state::save_instance(expr const & i) {
    if (m_num_instances >= m_config.m_max_instances) {
        if (!m_max_instances_exceeded) {
            lean_trace("ematch", tout() << "maximum number of ematching instances (" << m_config.m_max_instances << ") has been reached, "
                       << "set option ematch.max_instances to increase limit\n";);
        }
        m_max_instances_exceeded = true;
        return false;
    }
    if (m_instances.contains(i)) {
        return false;
    } else {
        m_num_instances++;
        m_instances.insert(i);
        return true;
    }
}

bool ematch_state::save_instance(expr const & lemma, buffer<expr> const & args) {
    expr key = mk_app(lemma, args);
    return save_instance(key);
}

struct ematch_fn {
    enum frame_kind { DefEqOnly, EqvOnly, Match, MatchSS /* match subsingleton */, Continue };
    typedef std::tuple<frame_kind, expr, expr> entry;
    typedef list<entry>                        state;
    typedef list<state>                        choice;

    type_context &             m_ctx;
    ematch_state &             m_ematch_state;
    congruence_closure &       m_cc;
    buffer<expr_pair> &        m_new_instances;

    state                      m_state;
    buffer<choice>             m_choice_stack;

    ematch_fn(type_context & ctx, ematch_state & ems, congruence_closure & cc, buffer<expr_pair> & new_insts):
        m_ctx(ctx), m_ematch_state(ems), m_cc(cc), m_new_instances(new_insts) {}

    void push_states(buffer<state> & new_states) {
        if (new_states.size() == 1) {
            lean_trace(name({"debug", "ematch"}), tout() << "(only one match)\n";);
            m_state = new_states[0];
        } else {
            lean_trace(name({"debug", "ematch"}), tout() << "# matches: " << new_states.size() << "\n";);
            m_state = new_states.back();
            new_states.pop_back();
            choice c = to_list(new_states);
            m_choice_stack.push_back(c);
            m_ctx.push_scope();
        }
    }

    bool is_eqv(expr const & p, expr const & t) {
        if (!has_expr_metavar(p)) {
            return m_cc.is_eqv(p, t) || m_ctx.is_def_eq(p, t);
        } else if (is_meta(p)) {
            expr const & m = get_app_fn(p);
            if (!m_ctx.is_assigned(m)) {
                expr p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
                expr t_type = m_ctx.infer(t);
                if (m_ctx.is_def_eq(p_type, t_type)) {
                    /* Types are definitionally equal. So, we just assign */
                    return m_ctx.is_def_eq(p, t);
                } else if (!has_expr_metavar(p_type) && !has_expr_metavar(t_type)) {
                    /* Check if types are provably equal and apply cast
                       Here is some background on this case. p is a metavariable ?m.
                       So, it should be the argument of some function application (f a_1 ... a_k ?m ...).
                       Reason: p is a subterm of a valid pattern.
                       Then, t should also be the argument of a function application (f b_1 ... b_k t ...).
                       Reason: how the ematching procedure works.
                       Moreover, the types of ?m and t should be of the form
                             ?m : A_{k+1}[a_1 ... a_k]
                             t  : A_{k+1}[b_1 ... b_k]
                       The function applications are type correct, and the type of f should be of the form:
                          f : Pi (x_1 : A_1) (x_2 : A_2[x_1]) ... (x_k : A_k[x_1, ... x_{k-1}]) (x_{k+1} : A_{k+1}[x_1, ..., x_k]) ..., B
                       The subproblems a_i == b_i have already been processed. So,
                       A[a_1 ... a_k] is probably congruent to A[b_1 ... b_k].
                       We say "probably" because we may miss some cases depending on how the equalities
                       have been processed. For example, A_{k+1}[...] may contain binders,
                       and we may not have visited them.
                       Important: we must process arguments from left to right. Otherwise, the "trick"
                       above will not work.
                    */
                    m_cc.internalize(p_type, false);
                    m_cc.internalize(t_type, false);
                    if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                        expr cast_H_t = mk_app(m_ctx, get_cast_name(), *H, t);
                        return m_ctx.is_def_eq(p, cast_H_t);
                    } else {
                        /* Types are not definitionally equal nor provably equal */
                        return false;
                    }
                } else {
                    /* Types are not definitionally equal, and we cannot check whether they are provably equal
                       using cc since they contain metavariables */
                    return false;
                }
            } else {
                expr new_p = m_ctx.instantiate_mvars(p);
                if (!has_expr_metavar(new_p))
                    return m_cc.is_eqv(new_p, t) || m_ctx.is_def_eq(new_p, t);
                else
                    return m_ctx.is_def_eq(new_p, t);
            }
        } else {
            return m_ctx.is_def_eq(p, t);
        }
    }

    /* If the eq equivalence class of `t` is heterogeneous, then even though
       `t` may fail to match because of its type, another element that is
       heterogeneously equal to `t`, but that has a different type, may match
       successfully. */
    bool match_leaf(expr const & p, expr const & t) {
        if (m_cc.in_heterogeneous_eqc(t)) {
            buffer<state> new_states;
            expr_set types_seen;
            expr it = t;
            do {
                expr it_type = m_ctx.infer(it);
                if (!types_seen.find(it_type)) {
                    types_seen.insert(it_type);
                    new_states.emplace_back(cons(entry(EqvOnly, p, it), m_state));
                }
                it = m_cc.get_next(it);
            } while (it != t);
            push_states(new_states);
            return true;
        } else {
            return is_eqv(p, t);
        }
    }

    bool match_args(state & s, buffer<expr> const & p_args, expr const & t) {
        optional<ext_congr_lemma> cg_lemma = m_cc.mk_ext_congr_lemma(t);
        if (!cg_lemma) return false;
        buffer<expr> t_args;
        expr const & fn = get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        if (cg_lemma->m_hcongr_lemma) {
            /* Lemma was created using mk_hcongr_lemma */
            fun_info finfo                 = get_fun_info(m_ctx, fn, t_args.size());
            list<ss_param_info> sinfo      = get_subsingleton_info(m_ctx, fn, t_args.size());
            list<param_info> const * it1   = &finfo.get_params_info();
            list<ss_param_info> const *it2 = &sinfo;
            buffer<entry> new_entries;
            for (unsigned i = 0; i < t_args.size(); i++) {
                if (*it1 && head(*it1).is_inst_implicit()) {
                    new_entries.emplace_back(DefEqOnly, p_args[i], t_args[i]);
                } else if (*it2 && head(*it2).is_subsingleton()) {
                    new_entries.emplace_back(MatchSS, p_args[i], t_args[i]);
                } else {
                    new_entries.emplace_back(Match, p_args[i], t_args[i]);
                }
                if (*it1) it1 = &tail(*it1);
                if (*it2) it2 = &tail(*it2);
            }
            s = to_list(new_entries.begin(), new_entries.end(), s);
            return true;
        } else {
            return false;
        }
    }

    bool process_match(expr const & p, expr const & t) {
        lean_trace(name({"debug", "ematch"}),
                   expr new_p      = m_ctx.instantiate_mvars(p);
                   expr new_p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "try process_match: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);
        if (!is_app(p)) {
            return match_leaf(p, t);
        }
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        if (m_ctx.is_mvar(fn)) {
            return match_leaf(p, t);
        }
        buffer<expr> candidates;
        expr t_fn;
        expr it = t;
        do {
            expr const & it_fn = get_app_fn(it);
            bool ok = false;
            if ((m_cc.is_congr_root(it) || m_cc.in_heterogeneous_eqc(it)) &&
                m_ctx.is_def_eq(it_fn, fn) &&
                get_app_num_args(it) == p_args.size()) {
                t_fn = it_fn;
                ok = true;
                candidates.push_back(it);
            }
            lean_trace(name({"debug", "ematch"}),
                       tout() << "candidate: " << it << "..." << (ok ? "ok" : "skip") << "\n";);
            it = m_cc.get_next(it);
        } while (it != t);

        if (candidates.empty()) {
            lean_trace(name({"debug", "ematch"}), tout() << "(no candidates)\n";);
            return false;
        }
        buffer<state> new_states;
        for (expr const & c : candidates) {
            state new_state = m_state;
            if (match_args(new_state, p_args, c)) {
                lean_trace(name({"debug", "ematch"}), tout() << "match: " << c << "\n";);
                new_states.push_back(new_state);
            }
        }
        push_states(new_states);
        return true;
    }

    bool process_continue(expr const & p) {
        lean_trace(name({"debug", "ematch"}), tout() << "process_continue: " << p << "\n";);
        buffer<expr> p_args;
        expr const & f = get_app_args(p, p_args);
        buffer<state> new_states;
        if (auto s = m_ematch_state.get_app_map().find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if (m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t)) {
                        state new_state = m_state;
                        if (match_args(new_state, p_args, t))
                            new_states.push_back(new_state);
                    }
                });
            if (new_states.empty()) {
                return false;
            } else if (new_states.size() == 1) {
                m_state = new_states[0];
                return true;
            } else {
                m_state = new_states.back();
                new_states.pop_back();
                choice c = to_list(new_states);
                m_choice_stack.push_back(c);
                m_ctx.push_scope();
                return true;
            }
        } else {
            return false;
        }
    }

    /* (Basic) subsingleton matching support: solve p =?= t when
       typeof(p) and typeof(t) are subsingletons */
    bool process_matchss(expr const & p, expr const & t) {
        lean_trace(name({"debug", "ematch"}),
                   expr new_p      = m_ctx.instantiate_mvars(p);
                   expr new_p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "process_matchss: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);

        if (!is_metavar(p)) {
            /* If p is not a metavariable we simply ignore it.
               We should improve this case in the future. */
            lean_trace(name({"debug", "ematch"}), tout() << "(p not a metavar)\n";);
            return true;
        }
        expr p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
        expr t_type = m_ctx.infer(t);
        if (m_ctx.is_def_eq(p_type, t_type)) {
            bool success = m_ctx.is_def_eq(p, t);
            lean_trace(name({"debug", "ematch"}),
                       tout() << "types are def_eq and assignment..." << (success ? "succeeded" : "failed") << "\n";);
            return success;
        } else {
            /* Check if the types are provably equal, and cast t */
            m_cc.internalize(p_type, false);
            if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                expr cast_H_t = mk_app(m_ctx, get_cast_name(), *H, t);
                bool success = m_ctx.is_def_eq(p, cast_H_t);
                lean_trace(name({"debug", "ematch"}),
                           tout() << "types can be proved equal and assignment..." << (success ? "succeeded" : "failed") << "\n";);
                return success;
            }
        }
        lean_trace(name({"debug", "ematch"}), tout() << "types cannot be proved equal\n";);
        return false;
    }

    bool is_done() const {
        return is_nil(m_state);
    }

    bool process_next() {
        lean_assert(!is_done());
        frame_kind kind; expr p, t;
        std::tie(kind, p, t) = head(m_state);
        m_state = tail(m_state);

        bool success;
        switch (kind) {
        case DefEqOnly:
            success = m_ctx.is_def_eq(p, t);
            lean_trace(name({"debug", "ematch"}),
                       expr new_p      = m_ctx.instantiate_mvars(p);
                       expr new_p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
                       expr t_type     = m_ctx.infer(t);
                       tout() << "must be def-eq: " << new_p << " : " << new_p_type
                       << "  =?= " << t << " : " << t_type
                       << " ... " << (success ? "succeeded" : "failed") << "\n";);
            return success;
        case Match:
            return process_match(p, t);
        case EqvOnly:
            success = is_eqv(p, t);
            lean_trace(name({"debug", "ematch"}),
                       expr new_p      = m_ctx.instantiate_mvars(p);
                       expr new_p_type = m_ctx.instantiate_mvars(m_ctx.infer(p));
                       expr t_type     = m_ctx.infer(t);
                       tout() << "must be eqv: " << new_p << " : " << new_p_type << " =?= "
                       << t << " : " << t_type << " ... " << (success ? "succeeded" : "failed") << "\n";);
            return success;
        case MatchSS:
            return process_matchss(p, t);
        case Continue:
            return process_continue(p);
        }
        lean_unreachable();
    }

    bool backtrack() {
        lean_trace(name({"debug", "ematch"}), tout() << "backtrack\n";);
        if (m_choice_stack.empty())
            return false;
        m_ctx.pop_scope();
        lean_assert(m_choice_stack.back());
        m_state = head(m_choice_stack.back());
        m_ctx.push_scope();
        m_choice_stack.back() = tail(m_choice_stack.back());
        if (!m_choice_stack.back())
            m_choice_stack.pop_back();
        return true;
    }

    void instantiate(hinst_lemma const & lemma) {
        list<bool> const * it = &lemma.m_is_inst_implicit;
        buffer<expr> lemma_args;
        for (expr const & mvar : lemma.m_mvars) {
            if (!m_ctx.is_assigned(mvar)) {
                if (!head(*it)) {
                    lean_trace(name({"debug", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unassigned argument not inst-implicit: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, argument is not instance implicit
                }
                auto new_val = m_ctx.mk_class_instance(m_ctx.infer(mvar));
                if (!new_val) {
                    lean_trace(name({"debug", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "cannot synthesize unassigned inst-implicit argument: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, instance could not be generated
                }
                if (!m_ctx.is_def_eq(mvar, *new_val)) {
                    lean_trace(name({"debug", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unable to assign inst-implicit argument: " << *new_val << " : " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, type error
                }
            }
            lemma_args.push_back(mvar);
            it = &tail(*it);
        }

        for (expr & lemma_arg : lemma_args) {
            lemma_arg = m_ctx.instantiate_mvars(lemma_arg);
            if (has_idx_metavar(lemma_arg)) {
                lean_trace(name({"debug", "ematch"}),
                           tout() << "instantiation failure [" << lemma.m_id << "], " <<
                           "there are unassigned metavariables\n";);
                return; // result contains temporary metavariables
            }
        }

        if (!m_ematch_state.save_instance(lemma.m_prop, lemma_args)) {
            return; // already added this instance
        }

        expr new_inst  = m_ctx.instantiate_mvars(lemma.m_prop);
        if (has_idx_metavar(new_inst))
            return; // result contains temporary metavariables

        lean_trace("ematch",
                   tout() << "instance [" << lemma.m_id << "]: " << new_inst << "\n";);
        expr new_proof = m_ctx.instantiate_mvars(lemma.m_proof);
        m_new_instances.emplace_back(new_inst, new_proof);
    }

    void search(hinst_lemma const & lemma) {
        while (true) {
            check_system("ematching");
            if (is_done()) {
                instantiate(lemma);
                if (!backtrack())
                    return;
            }
            if (!process_next()) {
                if (!backtrack())
                    return;
            }
        }
    }

    void clear_choice_stack() {
        for (unsigned i = 0; i < m_choice_stack.size(); i++) {
            m_ctx.pop_scope();
        }
        m_choice_stack.clear();
    }

    state mk_inital_state(buffer<expr> const & ps) {
        state s;
        unsigned i = ps.size();
        while (i > 1) {
            --i;
            s = cons(entry(Continue, ps[i], expr()), s);
        }
        return s;
    }

    void ematch_core(hinst_lemma const & lemma, state const & s, buffer<expr> const & p0_args, expr const & t) {
        lean_trace(name({"debug", "ematch"}),
                   tout() << "ematch " << lemma.m_id << " [using] " << t << "\n";);
        type_context::tmp_mode_scope scope(m_ctx, lemma.m_num_uvars, lemma.m_num_mvars);
        clear_choice_stack();
        m_state = s;
        if (!match_args(m_state, p0_args, t))
            return;
        search(lemma);
    }

    void ematch(hinst_lemma const & lemma, multi_pattern const & mp, expr const & t) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        state init_state = mk_inital_state(ps);
        buffer<expr> p0_args;
        get_app_args(ps[0], p0_args);
        ematch_core(lemma, init_state, p0_args, t);
    }

    void ematch(hinst_lemma const & lemma, expr const & t) {
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch(lemma, mp, t);
        }
    }

    void ematch_all_core(hinst_lemma const & lemma, buffer<expr> const & ps, bool filter) {
        expr const & p0  = ps[0];
        buffer<expr> p0_args;
        expr const & f   = get_app_args(p0, p0_args);
        unsigned gmt     = m_cc.get_gmt();
        state init_state = mk_inital_state(ps);
        if (expr_set const * s = m_ematch_state.get_app_map().find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if ((m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t)) &&
                        (!filter || m_cc.get_mt(t) == gmt)) {
                        ematch_core(lemma, init_state, p0_args, t);
                    }
                });
        }
    }

    void ematch_all(hinst_lemma const & lemma, multi_pattern const & mp, bool filter) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        if (filter) {
            for (unsigned i = 0; i < ps.size(); i++) {
                std::swap(ps[0], ps[i]);
                ematch_all_core(lemma, ps, filter);
                std::swap(ps[0], ps[i]);
            }
        } else {
            ematch_all_core(lemma, ps, filter);
        }
    }


    void ematch_all(hinst_lemma const & lemma, bool filter) {
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch_all(lemma, mp, filter);
        }
    }
};

void ematch(type_context & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t, buffer<expr_pair> & result) {
    ematch_fn(ctx, s, cc, result).ematch(lemma, t);
}

void ematch_all(type_context & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter, buffer<expr_pair> & result) {
    ematch_fn(ctx, s, cc, result).ematch_all(lemma, filter);
}

void initialize_ematch() {
    register_trace_class("ematch");
    register_trace_class(name({"debug", "ematch"}));
}
void finalize_ematch() {
}
}
