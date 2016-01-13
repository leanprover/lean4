/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "library/constants.h"
#include "library/idx_metavar.h"
#include "library/head_map.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/forward/pattern.h"
#include "library/blast/forward/forward_lemmas.h"
#include "library/blast/simplifier/simp_lemmas.h"

// TODO(Leo, Daniel): should we store all options at blast/options.cpp?
// Leo: I think we should only put the main options there, i.e.,
// the ones that are accessed/checked all the time. The config structure
// provides fast access to these options, and allows us to update them without
// using the expensive options object methods.
// Alternative design: each main module (forward/backward/simplifier/...) maintains
// its own config object.
#ifndef LEAN_DEFAULT_BLAST_EMATCH_MAX_INSTANCES
#define LEAN_DEFAULT_BLAST_EMATCH_MAX_INSTANCES 1000
#endif

namespace lean {
namespace blast {
#define lean_trace_ematch(Code) lean_trace(name({"blast", "ematch"}), Code)
#define lean_trace_event_ematch(Code) lean_trace(name({"blast", "event", "ematch"}), Code)
#define lean_trace_debug_ematch(Code) lean_trace(name({"debug", "blast", "ematch"}), Code)

static name * g_blast_ematch_max_instances = nullptr;

unsigned get_blast_ematch_max_instances(options const & o) {
    return o.get_unsigned(*g_blast_ematch_max_instances, LEAN_DEFAULT_BLAST_EMATCH_MAX_INSTANCES);
}

typedef rb_tree<expr, expr_quick_cmp> expr_set;
/* Branch extension for supporting heuristic instantiations methods.
   It contains
   1- mapping functions to its applications.
   2- set of lemmas that have been instantiated. */
class instances_branch_extension : public branch_extension {
    rb_map<head_index, expr_set, head_index::cmp> m_apps;
    expr_set                                      m_instances;
    unsigned                                      m_num_instances{0};
    unsigned                                      m_max_instances{0};
    bool                                          m_max_instances_exceeded{false};
public:
    instances_branch_extension() {}

    instances_branch_extension(instances_branch_extension const & src):
        m_apps(src.m_apps), m_instances(src.m_instances),
        m_num_instances(src.m_num_instances), m_max_instances(src.m_max_instances),
        m_max_instances_exceeded(src.m_max_instances_exceeded) {}

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

    virtual void initialized() override {
        m_max_instances = get_blast_ematch_max_instances(ios().get_options());
    }

    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx) override {
        collect_apps(h.get_type());
    }

    virtual void target_updated() override { collect_apps(curr_state().get_target()); }

    virtual branch_extension * clone() override { return new instances_branch_extension(*this); }

    bool max_instances_exceeded() const { return m_max_instances_exceeded; }

    bool save_instance(expr const & i) {
        if (m_num_instances >= m_max_instances) {
            if (!m_max_instances_exceeded) {
                lean_trace_ematch(tout() << "maximum number of ematching instances (" << m_max_instances << ") has been reached, "
                                  << "set option blast.ematch.max_instances to increase limit\n";);
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

    rb_map<head_index, expr_set, head_index::cmp> const & get_apps() const {
        return m_apps;
    }
};

static unsigned g_inst_ext_id = 0;
instances_branch_extension & get_inst_ext() {
    return static_cast<instances_branch_extension&>(curr_state().get_extension(g_inst_ext_id));
}

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
typedef rb_tree<hi_lemma, hi_lemma_cmp> hi_lemma_set;
struct ematch_branch_extension_core : public branch_extension {
    hi_lemma_set                                  m_lemmas;
    hi_lemma_set                                  m_new_lemmas;

    ematch_branch_extension_core() {}
    ematch_branch_extension_core(ematch_branch_extension_core const & src):
        m_lemmas(src.m_lemmas), m_new_lemmas(src.m_new_lemmas) {}
    virtual ~ematch_branch_extension_core() {}

    void register_lemma(hypothesis const & h) {
        if (is_pi(h.get_type()) && !is_arrow(h.get_type())) {
            try {
                m_new_lemmas.insert(mk_hi_lemma(h.get_self()));
            } catch (exception &) {}
        }
    }

    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx) override {
        register_lemma(h);
    }
};

/* Extension that populates initial lemma set using [forward] lemmas */
struct ematch_branch_extension : public ematch_branch_extension_core {
    virtual void initialized() override {
        forward_lemmas s = get_forward_lemmas(env());
        s.for_each([&](name const & n, unsigned prio) {
                try {
                    m_new_lemmas.insert(mk_hi_lemma(n, prio));
                } catch (exception & ex) {
                    lean_trace_event_ematch(tout() << "ematcher discarding [forward] '" << n << "', " << ex.what() << "\n";);
                }
            });
    }
    virtual branch_extension * clone() override { return new ematch_branch_extension(*this); }
};

static unsigned g_ematch_ext_id = 0;
ematch_branch_extension_core & get_ematch_ext() {
    return static_cast<ematch_branch_extension&>(curr_state().get_extension(g_ematch_ext_id));
}

/* Extension that populates initial lemma set using [simp] lemmas */
struct ematch_simp_branch_extension : public ematch_branch_extension_core {
    virtual void initialized() override {
        buffer<name> simp_lemmas;
        get_simp_lemmas(env(), simp_lemmas);
        for (name const & n : simp_lemmas) {
            try {
                m_new_lemmas.insert(mk_hi_simp_lemma(n, get_simp_lemma_priority(env(), n)));
            } catch (exception & ex) {
                lean_trace_event_ematch(tout() << "ematcher discarding [simp] '" << n << "', " << ex.what() << "\n";);
            }
        }
    }
    virtual branch_extension * clone() override { return new ematch_simp_branch_extension(*this); }
};

static unsigned g_ematch_simp_ext_id = 0;
ematch_branch_extension_core & get_ematch_simp_ext() {
    return static_cast<ematch_simp_branch_extension&>(curr_state().get_extension(g_ematch_simp_ext_id));
}

/* Auxiliary proof step used to bump proof depth */
struct noop_proof_step_cell : public proof_step_cell {
    virtual ~noop_proof_step_cell() {}
    virtual action_result resolve(expr const & pr) const override {
        return action_result::solved(pr);
    }
};

void initialize_ematch() {
    g_inst_ext_id        = register_branch_extension(new instances_branch_extension());
    g_ematch_ext_id      = register_branch_extension(new ematch_branch_extension());
    g_ematch_simp_ext_id = register_branch_extension(new ematch_simp_branch_extension());
    register_trace_class(name{"blast", "ematch"});
    register_trace_class(name{"blast", "event", "ematch"});
    register_trace_class(name{"debug", "blast", "ematch"});

    g_blast_ematch_max_instances = new name{"blast", "ematch", "max_instances"};

    register_unsigned_option(*g_blast_ematch_max_instances, LEAN_DEFAULT_BLAST_EMATCH_MAX_INSTANCES,
                             "(blast.ematch) max number of instances created by ematching based procedures");
}

void finalize_ematch() {}

struct ematch_fn {
    ematch_branch_extension_core & m_ext;
    instances_branch_extension &   m_inst_ext;
    blast_tmp_type_context         m_ctx;
    congruence_closure &           m_cc;

    enum frame_kind { DefEqOnly, Match, MatchSS /* match subsingleton */, Continue };

    typedef std::tuple<name, frame_kind, expr, expr> entry;
    typedef list<entry>                              state;
    typedef list<state>                              choice;

    state                      m_state;
    buffer<choice>             m_choice_stack;

    bool                       m_new_instances;

    /** If fwd == true, then use [forward] lemmas, otherwise use [simp] lemmas */
    ematch_fn(bool fwd = true):
        m_ext(fwd ? get_ematch_ext() : get_ematch_simp_ext()),
        m_inst_ext(get_inst_ext()),
        m_cc(get_cc()),
        m_new_instances(false) {
    }

    bool is_done() const {
        return is_nil(m_state);
    }

    bool is_eqv(name const & R, expr const & p, expr const & t) {
        if (!has_expr_metavar(p)) {
            return m_cc.is_eqv(R, p, t) || m_ctx->is_def_eq(p, t);
        } else if (is_meta(p)) {
            expr const & m = get_app_fn(p);
            if (!m_ctx->is_assigned(m)) {
                return m_ctx->is_def_eq(p, t);
            } else {
                expr new_p = m_ctx->instantiate_uvars_mvars(p);
                if (!has_expr_metavar(new_p))
                    return m_cc.is_eqv(R, new_p, t) || m_ctx->is_def_eq(new_p, t);
                else
                    return m_ctx->is_def_eq(new_p, t);
            }
        } else {
            return m_ctx->is_def_eq(p, t);
        }
    }

    bool match_args(state & s, name const & R, buffer<expr> const & p_args, expr const & t) {
        optional<ext_congr_lemma> cg_lemma = mk_ext_congr_lemma(R, t);
        if (!cg_lemma)
            return false;
        buffer<expr> t_args;
        expr const & fn = get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        if (cg_lemma->m_hcongr_lemma) {
            /* Lemma was created using mk_hcongr_lemma */
            lean_assert(is_standard(env()));
            fun_info finfo = get_fun_info(fn, t_args.size());
            list<param_info> const * pinfos = &finfo.get_params_info();
            lean_assert(length(*pinfos) == t_args.size());
            /* Process subsingletons first.
               We want them to be on the bottom of the "stack".
               That is, we want the other arguments to be processed first.
               Motivation: instantiate meta-variables in the subsingleton before we process it. */
            for (unsigned i = 0; i < t_args.size(); i++) {
                param_info const & pinfo = head(*pinfos);
                if (pinfo.is_subsingleton()) {
                    s = cons(entry(get_eq_name(), MatchSS, p_args[i], t_args[i]), s);
                }
                pinfos = &tail(*pinfos);
            }
            /* Process non-subsingletons */
            pinfos = &finfo.get_params_info();
            for (unsigned i = 0; i < t_args.size(); i++) {
                param_info const & pinfo = head(*pinfos);
                if (pinfo.is_inst_implicit()) {
                    s = cons(entry(get_eq_name(), DefEqOnly, p_args[i], t_args[i]), s);
                } else if (pinfo.is_subsingleton()) {
                    /* already processed in previous loop */
                } else {
                    s = cons(entry(get_eq_name(), Match, p_args[i], t_args[i]), s);
                }
                pinfos = &tail(*pinfos);
            }
        } else {
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
        }
        return true;
    }

    bool process_match(name const & R, expr const & p, expr const & t) {
        lean_trace_debug_ematch(tout() << "try process_match: "
                                << ppb(p) << " <=?=> " << ppb(t) << "\n";);
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
        if (auto s = m_inst_ext.get_apps().find(head_index(f))) {
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

    /* (Basic) subsingleton matching support: solve p =?= t when
       typeof(p) and typeof(t) are subsingletons */
    bool process_matchss(expr const & p, expr const & t) {
        lean_assert(is_standard(env()));
        if (!is_metavar(p)) {
            /* If p is not a metavariable we simply ignore it.
               We should improve this case in the future.
               TODO(Leo, Daniel): add debug.blast.ematch message here */
            return true;
        }
        expr p_type = m_ctx->instantiate_uvars_mvars(m_ctx->infer(p));
        expr t_type = m_ctx->infer(t);
        if (m_ctx->is_def_eq(p_type, t_type)) {
            return m_ctx->assign(p, t);
        } else {
            /* Check if the types are provably equal, and cast t */
            m_cc.internalize(get_eq_name(), p_type, false);
            if (auto H = m_cc.get_eqv_proof(get_eq_name(), t_type, p_type)) {
                expr cast_H_t = get_app_builder().mk_app(get_cast_name(), *H, t);
                return m_ctx->assign(p, cast_H_t);
            }
        }
        /* TODO(Leo, Daniel): add debug.blast.ematch message here */
        return false;
    }

    bool process_next() {
        lean_assert(!is_done());
        name R; frame_kind kind; expr p, t;
        std::tie(R, kind, p, t) = head(m_state);
        m_state = tail(m_state);
        // diagnostic(env(), ios()) << ">> " << R << ", " << ppb(p) << " =?= " << ppb(t) << "\n";
        switch (kind) {
        case DefEqOnly:
            lean_trace_debug_ematch(tout() << "must be def-eq: "
                                    << ppb(p) << " <=?=> " << ppb(t) << "...";);
            return m_ctx->is_def_eq(p, t);
        case Match:
            return process_match(R, p, t);
        case MatchSS:
            return process_matchss(p, t);
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
        if (!m_inst_ext.save_instance(new_inst))
            return; // already added this instance
        if (!m_new_instances) {
            trace_action("ematch");
        }
        lean_trace_ematch(tout() << "instance [" << ppb(lemma.m_expr) << "]: " << ppb(new_inst) << "\n";);
        m_new_instances = true;
        expr new_proof = m_ctx->instantiate_uvars_mvars(lemma.m_proof);
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
        if (auto s = m_inst_ext.get_apps().find(head_index(f))) {
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
                if (!m_inst_ext.max_instances_exceeded())
                    instantiate_lemma(l, filter);
            });
    }

    action_result operator()() {
        if (m_inst_ext.max_instances_exceeded())
            return action_result::failed();
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
        return ematch_fn(true)();
    else
        return action_result::failed();
}

action_result ematch_simp_action() {
    if (get_config().m_ematch)
        return ematch_fn(false)();
    else
        return action_result::failed();
}
}}
