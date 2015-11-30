/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/idx_metavar.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/forward/pattern.h"

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
    hi_lemma_set                           m_lemmas;
    hi_lemma_set                           m_new_lemmas;
    rb_map<expr, expr_set, expr_quick_cmp> m_apps;
    name_set                               m_initialized;

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
            if (is_constant(f) && !m_initialized.contains(const_name(f))) {
                m_initialized.insert(const_name(f));
                if (auto lemmas = get_hi_lemma_index(env()).find(const_name(f))) {
                    for (hi_lemma const & lemma : *lemmas) {
                        m_new_lemmas.insert(lemma);
                    }
                }
            }
            if ((is_constant(f) && !is_no_pattern(env(), const_name(f))) ||
                (is_local(f))) {
                expr_set s;
                if (auto old_s = m_apps.find(f))
                    s = *old_s;
                s.insert(e);
                m_apps.insert(f, s);
            }
            for (expr const & arg : args) {
                collect_apps(arg);
            }
            break;
        }}
    }

    void register_lemma(hypothesis const & h) {
        if (is_pi(h.get_type()) && !is_arrow(h.get_type())) {
            blast_tmp_type_context ctx;
            try {
                m_new_lemmas.insert(mk_hi_lemma(*ctx, h.get_self()));
            } catch (exception &) {}
        }
    }

    virtual ~ematch_branch_extension() {}
    virtual branch_extension * clone() override { return new ematch_branch_extension(*this); }
    virtual void initialized() override {}
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx) override {
        collect_apps(h.get_type());
        register_lemma(h);
    }
    virtual void hypothesis_deleted(hypothesis const &, hypothesis_idx) override {}
    virtual void target_updated() override { collect_apps(curr_state().get_target()); }
};

void initialize_ematch() {
    g_ext_id = register_branch_extension(new ematch_branch_extension());
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

    bool process_match(name const & R, expr const & p, expr const & t) {
        if (!is_app(p))
            return is_eqv(R, p, t);
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        if (m_ctx->is_mvar(fn))
            return is_eqv(R, p, t);
        buffer<expr> candidates;
        expr it = t;
        do {
            if (m_cc.is_congr_root(R, t) && m_ctx->is_def_eq(get_app_fn(it), fn) &&
                get_app_num_args(it) == p_args.size()) {
                candidates.push_back(it);
            }
            it = m_cc.get_next(R, it);
        } while (it != t);
        if (candidates.empty())
            return false;
        optional<ext_congr_lemma> lemma = mk_ext_congr_lemma(R, fn, p_args.size());
        if (!lemma)
            return false;
        buffer<state> new_states;
        for (expr const & c : candidates) {
            buffer<expr> c_args;
            get_app_args(c, c_args);
            lean_assert(c_args.size() == p_args.size());
            state new_state = m_state;
            auto const * r_names = &lemma->m_rel_names;
            for (unsigned i = 0; i < p_args.size(); i++) {
                lean_assert(*r_names);
                if (auto Rc = head(*r_names)) {
                    new_state = cons(entry(*Rc, Match, p_args[i], c_args[i]), new_state);

                } else {
                    new_state = cons(entry(get_eq_name(), DefEqOnly, p_args[i], c_args[i]), new_state);
                }
                r_names = &tail(*r_names);
            }
            new_states.push_back(new_state);
        }
        lean_assert(candidates.size() == new_states.size());
        if (candidates.size() == 1) {
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

    bool process_continue(expr const &) {
        // TODO(Leo):
        return false;
    }

    bool process_next() {
        lean_assert(!is_done());
        name R; frame_kind kind; expr p, t;
        std::tie(R, kind, p, t) = head(m_state);
        m_state = tail(m_state);
        diagnostic(env(), ios()) << ">> " << R << ", " << ppb(p) << " =?= " << ppb(t) << "\n";
        switch (kind) {
        case DefEqOnly:
            return m_ctx->is_def_eq(p, t);
        case Match:
            return process_match(R, p, t);
        case Continue:
            return process_continue(p);
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
        std::cout << "FOUND\n";
        for (expr const & mvar : lemma.m_mvars) {
            diagnostic(env(), ios()) << "[" << mvar << "] := " << ppb(m_ctx->instantiate_uvars_mvars(mvar)) << "\n";
        }
    }

    void search(hi_lemma const & lemma) {
        while (true) {
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
        if (auto s = m_ext.m_apps.find(f)) {
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
                        optional<ext_congr_lemma> cg_lemma = mk_ext_congr_lemma(R, f, p0_args.size());
                        if (!cg_lemma)
                            return;
                        buffer<expr> t_args;
                        get_app_args(t, t_args);
                        if (p0_args.size() != t_args.size())
                            return;
                        auto const * r_names = &cg_lemma->m_rel_names;
                        for (unsigned i = 0; i < p0_args.size(); i++) {
                            lean_assert(*r_names);
                            if (auto Rc = head(*r_names)) {
                                m_state = cons(entry(*Rc, Match, p0_args[i], t_args[i]), m_state);

                            } else {
                                m_state = cons(entry(get_eq_name(), DefEqOnly, p0_args[i], t_args[i]), m_state);
                            }
                            r_names = &tail(*r_names);
                        }
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
