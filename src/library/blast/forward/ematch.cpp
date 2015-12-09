/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/interrupt.h"
#include "library/constants.h"
#include "library/idx_metavar.h"
#include "library/head_map.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/forward/pattern.h"
#include "library/blast/forward/forward_lemma_set.h"

namespace lean {
namespace blast {
/*
When a hypothesis hidx is activated:
1- Traverse its type and for each f-application.
   If it is the first f-application found, and f is a constant then
   retrieve lemmas which contain a multi-pattern starting with f.

2- If hypothesis is a proposition and a quantifier,
try to create a hi-lemma for it, and add it to
set of recently activated hi_lemmas

E-match round action

1- For each active hi-lemma L, and mulit-pattern P,
   If L has been recently activated, then we ematch ignoring
   gmt.

   If L has been processed before, we try to ematch starting
   at each each element of the multi-pattern.
   We only consider the head f-applications that have a mt
   equal to gmt

*/
typedef rb_tree<expr, expr_quick_cmp> expr_set;
typedef rb_tree<hi_lemma, hi_lemma_cmp> hi_lemma_set;
static unsigned g_ext_id = 0;
struct ematch_branch_extension : public branch_extension {
    hi_lemma_set                                  m_lemmas;
    hi_lemma_set                                  m_new_lemmas;
    rb_map<head_index, expr_set, head_index::cmp> m_apps;
    expr_set                                      m_instances;

    ematch_branch_extension() {}
    ematch_branch_extension(ematch_branch_extension const &) {}

    void collect_apps(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Var:      case expr_kind::Sort:
        case expr_kind::Constant: case expr_kind::Meta:
        case expr_kind::Local:    case expr_kind::Lambda:
            break;
        case expr_kind::Pi:
            if (is_arrow(e) && is_prop(e)) {
                collect_apps(binding_domain(e));
                collect_apps(binding_body(e));
            }
            break;
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(e); i++)
                collect_apps(macro_arg(e, i));
            break;
        case expr_kind::App: {
            buffer<expr> args;
            expr const & f = get_app_args(e, args);
            if ((is_constant(f) && !is_no_pattern(env(), const_name(f))) ||
                (is_local(f))) {
                expr_set s;
                if (auto old_s = m_apps.find(head_index(f)))
                    s = *old_s;
                s.insert(e);
                m_apps.insert(head_index(f), s);
            }
            for (expr const & arg : args) {
                collect_apps(arg);
            }
            break;
        }}
    }

    void register_lemma(hypothesis const & h) {
        if (is_pi(h.get_type()) && !is_arrow(h.get_type())) {
            try {
                m_new_lemmas.insert(mk_hi_lemma(h.get_self()));
            } catch (exception &) {}
        }
    }

    virtual ~ematch_branch_extension() {}
    virtual branch_extension * clone() override { return new ematch_branch_extension(*this); }
    virtual void initialized() override {
        forward_lemma_set s = get_forward_lemma_set(env());
        s.for_each([&](name const & n, unsigned prio) {
                try {
                    m_new_lemmas.insert(mk_hi_lemma(n, prio));
                } catch (exception &) {}
            });
    }
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx) override {
        collect_apps(h.get_type());
        register_lemma(h);
    }
    virtual void hypothesis_deleted(hypothesis const &, hypothesis_idx) override {}
    virtual void target_updated() override { collect_apps(curr_state().get_target()); }
};

/* Auxiliary proof step used to bump proof depth */
struct noop_proof_step_cell : public proof_step_cell {
    virtual ~noop_proof_step_cell() {}
    virtual action_result resolve(expr const & pr) const override {
        return action_result::solved(pr);
    }
};

void initialize_ematch() {
    g_ext_id = register_branch_extension(new ematch_branch_extension());
    register_trace_class(name{"blast", "ematch"});
}

void finalize_ematch() {}

struct ematch_fn {
    ematch_branch_extension &  m_ext;
    blast_tmp_type_context     m_ctx;
    congruence_closure &       m_cc;

    enum frame_kind { DefEqOnly, Match, Continue };

    typedef std::tuple<name, frame_kind, expr, expr> entry;
    typedef list<entry>                              state;
    typedef list<state>                              choice;

    state                      m_state;
    buffer<choice>             m_choice_stack;

    bool                       m_new_instances;

    ematch_fn():
        m_ext(static_cast<ematch_branch_extension&>(curr_state().get_extension(g_ext_id))),
        m_cc(get_cc()),
        m_new_instances(false) {
    }

    bool is_done() const {
        return is_nil(m_state);
    }

    bool is_eqv(name const & R, expr const & p, expr const & t) {
        if (!has_expr_metavar(p))
            return m_cc.is_eqv(R, p, t) || m_ctx->is_def_eq(p, t);
        else
            return m_ctx->is_def_eq(p, t);
    }

    bool match_args(state & s, name const & R, buffer<expr> const & p_args, expr const & t) {
        optional<ext_congr_lemma> cg_lemma = mk_ext_congr_lemma(R, get_app_fn(t), p_args.size());
        if (!cg_lemma)
            return false;
        buffer<expr> t_args;
        get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        auto const * r_names = &cg_lemma->m_rel_names;
        for (unsigned i = 0; i < p_args.size(); i++) {
            lean_assert(*r_names);
            if (auto Rc = head(*r_names)) {
                s = cons(entry(*Rc, Match, p_args[i], t_args[i]), s);
            } else {
                s = cons(entry(get_eq_name(), DefEqOnly, p_args[i], t_args[i]), s);
            }
            r_names = &tail(*r_names);
        }
        return true;
    }

    bool process_match(name const & R, expr const & p, expr const & t) {
        if (!is_app(p))
            return is_eqv(R, p, t);
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        if (m_ctx->is_mvar(fn))
            return is_eqv(R, p, t);
        buffer<expr> candidates;
        expr t_fn;
        expr it = t;
        do {
            expr const & it_fn = get_app_fn(it);
            if (m_cc.is_congr_root(R, it) && m_ctx->is_def_eq(it_fn, fn) &&
                get_app_num_args(it) == p_args.size()) {
                t_fn = it_fn;
                candidates.push_back(it);
            }
            it = m_cc.get_next(R, it);
        } while (it != t);
        if (candidates.empty())
            return false;
        buffer<state> new_states;
        for (expr const & c : candidates) {
            state new_state = m_state;
            if (match_args(new_state, R, p_args, c)) {
                new_states.push_back(new_state);
            }
        }
        if (new_states.size() == 1) {
            m_state = new_states[0];
            return true;
        } else {
            m_state = new_states.back();
            new_states.pop_back();
            choice c = to_list(new_states);
            m_choice_stack.push_back(c);
            m_ctx->push();
            return true;
        }
    }

    bool process_continue(name const & R, expr const & p) {
        buffer<expr> p_args;
        expr const & f = get_app_args(p, p_args);
        buffer<state> new_states;
        if (auto s = m_ext.m_apps.find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if (m_cc.is_congr_root(R, t)) {
                        state new_state = m_state;
                        if (match_args(new_state, R, p_args, t))
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
                m_ctx->push();
                return true;
            }
        } else {
            return false;
        }
    }

    bool process_next() {
        lean_assert(!is_done());
        name R; frame_kind kind; expr p, t;
        std::tie(R, kind, p, t) = head(m_state);
        m_state = tail(m_state);
        // diagnostic(env(), ios()) << ">> " << R << ", " << ppb(p) << " =?= " << ppb(t) << "\n";
        switch (kind) {
        case DefEqOnly:
            return m_ctx->is_def_eq(p, t);
        case Match:
            return process_match(R, p, t);
        case Continue:
            return process_continue(R, p);
        }
        lean_unreachable();
    }

    bool backtrack() {
        if (m_choice_stack.empty())
            return false;
        m_ctx->pop();
        lean_assert(m_choice_stack.back());
        m_state = head(m_choice_stack.back());
        m_ctx->push();
        m_choice_stack.back() = tail(m_choice_stack.back());
        if (!m_choice_stack.back())
            m_choice_stack.pop_back();
        return true;
    }

    void instantiate(hi_lemma const & lemma) {
        list<bool> const * it = &lemma.m_is_inst_implicit;
        for (expr const & mvar : lemma.m_mvars) {
            if (!m_ctx->get_assignment(mvar)) {
                if (!head(*it))
                    return; // fail, argument is not instance implicit
                auto new_val = m_ctx->mk_class_instance(m_ctx->infer(mvar));
                if (!new_val)
                    return; // fail, instance could not be generated
                if (!m_ctx->assign(mvar, *new_val))
                    return; // fail, type error
            }
            it = &tail(*it);
        }
        expr new_inst  = normalize(m_ctx->instantiate_uvars_mvars(lemma.m_prop));
        if (has_idx_metavar(new_inst))
            return; // result contains temporary metavariables
        if (m_ext.m_instances.contains(new_inst))
            return; // already added this instance
        if (!m_new_instances) {
            trace_action("ematch");
        }
        lean_trace(name({"blast", "ematch"}), tout() << "instance: " << ppb(new_inst) << "\n";);
        m_new_instances = true;
        expr new_proof = m_ctx->instantiate_uvars_mvars(lemma.m_proof);
        m_ext.m_instances.insert(new_inst);
        curr_state().mk_hypothesis(new_inst, new_proof);
    }

    void search(hi_lemma const & lemma) {
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

    void instantiate_lemma_using(hi_lemma const & lemma, buffer<expr> const & ps, bool filter) {
        expr const & p0 = ps[0];
        buffer<expr> p0_args;
        expr const & f  = get_app_args(p0, p0_args);
        name const & R  = is_prop(p0) ? get_iff_name() : get_eq_name();
        unsigned gmt    = m_cc.get_gmt();
        if (auto s = m_ext.m_apps.find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if (m_cc.is_congr_root(R, t) && (!filter || m_cc.get_mt(R, t) == gmt)) {
                        m_ctx->clear();
                        m_ctx->set_next_uvar_idx(lemma.m_num_uvars);
                        m_ctx->set_next_mvar_idx(lemma.m_num_mvars);
                        state s;
                        unsigned i = ps.size();
                        while (i > 1) {
                            --i;
                            s = cons(entry(name(), Continue, ps[i], expr()), s);
                        }
                        m_choice_stack.clear();
                        m_state = s;
                        if (!match_args(m_state, R, p0_args, t))
                            return;
                        search(lemma);
                    }
                });
        }
    }

    void instantiate_lemma_using(hi_lemma const & lemma, multi_pattern const & mp, bool filter) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        if (filter) {
            for (unsigned i = 0; i < ps.size(); i++) {
                std::swap(ps[0], ps[i]);
                instantiate_lemma_using(lemma, ps, filter);
                std::swap(ps[0], ps[i]);
            }
        } else {
            instantiate_lemma_using(lemma, ps, filter);
        }
    }

    void instantiate_lemma(hi_lemma const & lemma, bool filter) {
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            instantiate_lemma_using(lemma, mp, filter);
        }
    }

    /* (Try to) instantiate lemmas in \c s. If \c filter is true, then use gmt optimization. */
    void instantiate_lemmas(hi_lemma_set const & s, bool filter) {
        s.for_each([&](hi_lemma const & l) {
                instantiate_lemma(l, filter);
            });
    }

    action_result operator()() {
        instantiate_lemmas(m_ext.m_new_lemmas, false);
        instantiate_lemmas(m_ext.m_lemmas, true);
        m_ext.m_lemmas.merge(m_ext.m_new_lemmas);
        m_ext.m_new_lemmas = hi_lemma_set();
        m_cc.inc_gmt();
        if (m_new_instances) {
            curr_state().push_proof_step(new noop_proof_step_cell());
            return action_result::new_branch();
        } else {
            return action_result::failed();
        }
    }
};

action_result ematch_action() {
    if (get_config().m_ematch)
        return ematch_fn()();
    else
        return action_result::failed();
}
}}
