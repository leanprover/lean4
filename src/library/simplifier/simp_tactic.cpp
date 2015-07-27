/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/app_builder.h"
#include "library/relation_manager.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/simplifier/ceqv.h"
#include "library/simplifier/simp_tactic.h"
#include "library/simplifier/simp_rule_set.h"

#ifndef LEAN_DEFAULT_SIMP_SINGLE_PASS
#define LEAN_DEFAULT_SIMP_SINGLE_PASS false
#endif

#ifndef LEAN_DEFAULT_SIMP_BOTTOM_UP
#define LEAN_DEFAULT_SIMP_BOTTOM_UP true
#endif

#ifndef LEAN_DEFAULT_SIMP_BETA_ETA
#define LEAN_DEFAULT_SIMP_BETA_ETA true
#endif

#ifndef LEAN_DEFAULT_SIMP_IOTA
#define LEAN_DEFAULT_SIMP_IOTA true
#endif

#ifndef LEAN_DEFAULT_SIMP_MEMOIZE
#define LEAN_DEFAULT_SIMP_MEMOIZE true
#endif

#ifndef LEAN_DEFAULT_SIMP_MAX_STEPS
#define LEAN_DEFAULT_SIMP_MAX_STEPS 10000
#endif

#ifndef LEAN_DEFAULT_SIMP_TRACE
#define LEAN_DEFAULT_SIMP_TRACE false
#endif

#ifndef LEAN_DEFAULT_SIMP_ASSUMPTIONS
#define LEAN_DEFAULT_SIMP_ASSUMPTIONS false
#endif

#ifndef LEAN_DEFAULT_SIMP_FUNEXT
#define LEAN_DEFAULT_SIMP_FUNEXT true
#endif

#ifndef LEAN_DEFAULT_SIMP_PROPEXT
#define LEAN_DEFAULT_SIMP_PROPEXT true
#endif

namespace lean {
name const * g_simp_single_pass = nullptr;
name const * g_simp_bottom_up   = nullptr;
name const * g_simp_beta_eta    = nullptr;
name const * g_simp_iota        = nullptr;
name const * g_simp_memoize     = nullptr;
name const * g_simp_max_steps   = nullptr;
name const * g_simp_trace       = nullptr;
name const * g_simp_assumptions = nullptr;
name const * g_simp_funext      = nullptr;
name const * g_simp_propext     = nullptr;

bool get_simp_single_pass(options const & opts) {
    return opts.get_bool(*g_simp_single_pass, LEAN_DEFAULT_SIMP_SINGLE_PASS);
}

bool get_simp_bottom_up(options const & opts) {
    return opts.get_bool(*g_simp_bottom_up, LEAN_DEFAULT_SIMP_BOTTOM_UP);
}

bool get_simp_beta_eta(options const & opts) {
    return opts.get_bool(*g_simp_beta_eta, LEAN_DEFAULT_SIMP_BETA_ETA);
}

bool get_simp_iota(options const & opts) {
    return opts.get_bool(*g_simp_iota, LEAN_DEFAULT_SIMP_IOTA);
}

bool get_simp_memoize(options const & opts) {
    return opts.get_bool(*g_simp_memoize, LEAN_DEFAULT_SIMP_MEMOIZE);
}

unsigned get_simp_max_steps(options const & opts) {
    return opts.get_bool(*g_simp_max_steps, LEAN_DEFAULT_SIMP_MAX_STEPS);
}

bool get_simp_trace(options const & opts) {
    return opts.get_bool(*g_simp_trace, LEAN_DEFAULT_SIMP_TRACE);
}

bool get_simp_assumptions(options const & opts) {
    return opts.get_bool(*g_simp_assumptions, LEAN_DEFAULT_SIMP_ASSUMPTIONS);
}

bool get_simp_funext(options const & opts) {
    return opts.get_bool(*g_simp_funext, LEAN_DEFAULT_SIMP_FUNEXT);
}

bool get_simp_propext(options const & opts) {
    return opts.get_bool(*g_simp_propext, LEAN_DEFAULT_SIMP_PROPEXT);
}

expr const * g_simp_tactic = nullptr;

expr mk_simp_tactic_expr(buffer<expr> const & ls, buffer<name> const & ns,
                         buffer<name> const & ex, optional<expr> const & pre_tac,
                         location const & loc) {
    expr e  = mk_expr_list(ls.size(), ls.data());
    expr n  = ids_to_tactic_expr(ns);
    expr x  = ids_to_tactic_expr(ex);
    expr t;
    if (pre_tac) {
        t = mk_app(mk_constant(get_option_some_name()), *pre_tac);
    } else {
        t = mk_constant(get_option_none_name());
    }
    expr l = mk_location_expr(loc);
    expr r = mk_app({*g_simp_tactic, e, n, x, t, l});
    return r;
}

class simp_tactic_fn {
public:
    enum res_kind { Simplified, Solved, DidNothing };
private:
    environment      m_env;
    io_state         m_ios;
    name_generator   m_ngen;
    elaborate_fn     m_elab;
    optional<tactic> m_tactic;

    type_checker     m_elab_tc;
    app_builder      m_app_builder;


    // transient state
    unsigned         m_steps;
    goal             m_g;
    substitution     m_subst;
    // Remark: the following buffer contains pre-terms that need to be elaborated.
    // The 'simp at *' is not very efficient in the current implementation.
    // If we have N hypotheses, then m_lemmas_to_process will be processed N+1 times.
    buffer<expr>     m_lemmas_to_process;

    simp_rule_sets   m_simp_sets;

    // configuration options
    bool     m_single_pass;
    bool     m_bottom_up;
    bool     m_beta_eta;
    bool     m_iota;
    bool     m_memoize;
    unsigned m_max_steps;
    bool     m_trace;
    bool     m_assumptions;
    bool     m_funext;
    bool     m_propext;
    bool     m_standard;

    io_state_stream out() const { return regular(m_env, m_ios); }

    void set_options(environment const & env, options const & o) {
        m_single_pass = get_simp_single_pass(o);
        m_bottom_up   = get_simp_bottom_up(o);
        m_beta_eta    = get_simp_beta_eta(o);
        m_iota        = get_simp_iota(o);
        m_memoize     = get_simp_memoize(o);
        m_max_steps   = get_simp_max_steps(o);
        m_trace       = get_simp_trace(o);
        m_assumptions = get_simp_assumptions(o);
        if (is_standard(env)) {
            m_funext   = get_simp_funext(o) && env.find(get_funext_name());
            m_propext  = get_simp_propext(o) && env.find(get_propext_name());
            m_standard = true;
        } else {
            // TODO(Leo): add support for function extensionality in HoTT mode
            m_funext      = false;
            m_propext     = false;
            m_standard    = false;
        }
    }

    // Add lemmas and assumptions to m_simp_set.
    // If hidx is none, then we are elaborating the conclusion, otherwise we are elaborating hypothesis hidx.
    // This method destructively updates m_simp_set
    void elaborate_lemmas(optional<unsigned> hidx) {
        name user("user");
        for (expr const & l : m_lemmas_to_process) {
            try {
                expr new_l; constraints cs;
                bool report_unassigned = true;
                std::tie(new_l, m_subst, cs) = m_elab(m_g, m_ngen.mk_child(), l, none_expr(), m_subst, report_unassigned);
                if (cs)
                    throw tactic_exception("invalid 'simp' tactic, fail to resolve generated constraints");
                expr new_e = head_beta_reduce(m_elab_tc.infer(new_l).first);
                m_simp_sets = add(m_elab_tc, m_simp_sets, user, new_e, new_l);
            } catch (exception &) {
                if (!hidx) {
                    // processing conclusion, then report the error
                    throw;
                }
            }
        }
        if (m_assumptions) {
            name assump("assumption");
            buffer<expr> hyps;
            m_g.get_hyps(hyps);
            unsigned end = hidx ? *hidx : hyps.size();
            for (unsigned i = 0; i < end; i++) {
                expr H      = hyps[i];
                expr H_type = mlocal_type(H);
                expr rel, lhs, rhs;
                if (is_simp_relation(m_env, H_type, rel, lhs, rhs)) {
                    // TODO(Leo): we are currently flipping equations when lhs < rhs.
                    // Should we remove this automatic flipping?
                    if (get_weight(lhs) >= get_weight(rhs)) {
                        m_simp_sets = add(m_elab_tc, m_simp_sets, assump, H_type, H);
                    } else {
                        // lhs is "smaller" than rhs
                        // so we try to apply symmetry if available
                        if (!is_constant(rel))
                            continue;
                        name op   = const_name(rel);
                        auto rel_info = get_relation_info(m_env, op);
                        auto info = get_symm_extra_info(m_env, op);
                        if (!info || !rel_info)
                            continue; // relation is not symmetric
                        buffer<expr> args;
                        get_app_args(H_type, args);
                        expr tmp = args[rel_info->get_lhs_pos()];
                        args[rel_info->get_lhs_pos()] = args[rel_info->get_rhs_pos()];
                        args[rel_info->get_rhs_pos()] = tmp;
                        H_type = mk_app(rel, args);
                        if (auto new_H = m_app_builder.mk_app(info->m_name, H)) {
                            H = *new_H;
                            m_simp_sets = add(m_elab_tc, m_simp_sets, assump, H_type, H);
                        }
                    }
                }
            }
        }
    }

    res_kind simp_conclusion() {
        elaborate_lemmas(optional<unsigned>());
        if (m_trace) {
            out() << m_simp_sets;
        }
        // TODO(Leo)
        return DidNothing;
    }

    bool simp_hyp(unsigned hidx) {
        flet<simp_rule_sets> save(m_simp_sets, m_simp_sets);
        elaborate_lemmas(optional<unsigned>(hidx));
        // TODO(Leo)
        return false;
    }

    // Initialize m_simp_set with information that is context independent
    void init_simp_set(buffer<name> const & ns, buffer<name> const & ex) {
        // Remark: we cannot initialize explicitly provided lemmas here
        // since some of them may depend on hypotheses.
        m_simp_sets = get_simp_rule_sets(m_env);
        for (name const & n : ns) {
            simp_rule_sets tmp_simp_set = get_simp_rule_sets(m_env, n);
            m_simp_sets = join(m_simp_sets, tmp_simp_set);
        }
        m_simp_sets.erase_simp(ex);
    }

public:
    simp_tactic_fn(environment const & env, io_state const & ios, name_generator && ngen, elaborate_fn const & elab,
                   buffer<expr> const & ls, buffer<name> const & ns, buffer<name> const & ex,
                   optional<tactic> const & tac):
        m_env(env), m_ios(ios), m_ngen(ngen), m_elab(elab), m_tactic(tac), m_elab_tc(m_env), m_app_builder(m_elab_tc),
        m_lemmas_to_process(ls) {
        set_options(env, m_ios.get_options());
        init_simp_set(ns, ex);
    }

    std::tuple<res_kind, goal, substitution> operator()(goal const & g, location const & loc, substitution const & s) {
        m_g     = g;
        m_subst = s;
        if (loc.is_goal_only()) {
            res_kind k = simp_conclusion();
            return std::make_tuple(k, m_g, m_subst);
        } else {
            buffer<expr> hyps;
            m_g.get_hyps(hyps);
            bool progress = false;
            unsigned hidx = 0;
            for (expr const & h : hyps) {
                if (loc.includes_hypothesis(local_pp_name(h))) {
                    if (simp_hyp(hidx))
                        progress = true;
                }
                hidx++;
            }
            if (loc.includes_goal()) {
                res_kind k = simp_conclusion();
                if (k == DidNothing && progress)
                    k = Simplified;
                return std::make_tuple(k, m_g, m_subst);
            } else {
                return std::make_tuple(progress ? Simplified : DidNothing, m_g, m_subst);
            }
        }
    }
};

tactic mk_simp_tactic(elaborate_fn const & elab, buffer<expr> const & ls, buffer<name> const & ns,
                      buffer<name> const & ex, optional<tactic> tac, location const & loc) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            goal const & g = head(gs);
            name_generator new_ngen  = s.get_ngen();
            simp_tactic_fn simp(env, ios, new_ngen.mk_child(), elab, ls, ns, ex, tac);
            goal new_g; simp_tactic_fn::res_kind k; substitution new_subst = s.get_subst();
            std::tie(k, new_g, new_subst) = simp(g, loc, new_subst);
            switch (k) {
            case simp_tactic_fn::Simplified: {
                proof_state new_s(s, cons(new_g, tail(gs)), new_subst, new_ngen);
                return some_proof_state(new_s);
            }
            case simp_tactic_fn::Solved: {
                proof_state new_s(s, tail(gs), new_subst, new_ngen);
                return some_proof_state(new_s);
            }
            case simp_tactic_fn::DidNothing:
                return none_proof_state();
            }
            lean_unreachable();
        });
}

void initialize_simp_tactic() {
    name simp_name{"tactic", "simp_tac"};
    g_simp_tactic = new expr(mk_constant(simp_name));

    register_tac(simp_name,
                 [](type_checker & tc, elaborate_fn const & elab, expr const & e, pos_info_provider const * p) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 5)
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, incorrect number of arguments");
                     buffer<expr> lemmas;
                     get_tactic_expr_list_elements(args[0], lemmas, "invalid 'simp' tactic, invalid argument #1");
                     buffer<name> ns, ex;
                     get_tactic_id_list_elements(args[1], ns, "invalid 'simp' tactic, invalid argument #2");
                     get_tactic_id_list_elements(args[2], ex, "invalid 'simp' tactic, invalid argument #3");
                     optional<tactic> tac;
                     expr A, t;
                     if (is_some(args[3], A, t)) {
                         tac = expr_to_tactic(tc, elab, t, p);
                     } else if (is_none(args[3], A)) {
                         // do nothing
                     } else {
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, invalid argument #4");
                     }
                     check_tactic_expr(args[4], "invalid 'simp' tactic, invalid argument #5");
                     expr loc_expr = get_tactic_expr_expr(args[4]);
                     if (!is_location_expr(loc_expr))
                         throw expr_to_tactic_exception(e, "invalid 'simp' tactic, invalid argument #5");
                     location loc = get_location_expr_location(loc_expr);
                     return mk_simp_tactic(elab, lemmas, ns, ex, tac, loc);
                 });


    g_simp_single_pass = new name{"simp", "single_pass"};
    register_bool_option(*g_simp_single_pass, LEAN_DEFAULT_SIMP_SINGLE_PASS,
                         "(simp tactic) if false then the simplifier keeps applying simplifications as long as possible");

    g_simp_bottom_up = new name{"simp", "bottom_up"};
    register_bool_option(*g_simp_bottom_up, LEAN_DEFAULT_SIMP_BOTTOM_UP,
                         "(simp tactic) if true the simplifier uses a bottom up rewriting strategy, otherwise it uses top down");

    g_simp_beta_eta = new name{"simp", "beta_eta"};
    register_bool_option(*g_simp_beta_eta, LEAN_DEFAULT_SIMP_BETA_ETA,
                         "(simp tactic) if true the simplifier applies beta and eta reduction");

    g_simp_iota = new name{"simp", "iota"};
    register_bool_option(*g_simp_iota, LEAN_DEFAULT_SIMP_IOTA,
                         "(simp tactic) if true the simplifier applies iota reduction");

    g_simp_memoize = new name{"simp", "memoize"};
    register_bool_option(*g_simp_memoize, LEAN_DEFAULT_SIMP_MEMOIZE,
                         "(simp tactic) if true the simplifier caches intermediate results");

    g_simp_max_steps = new name{"simp", "max_steps"};
    register_unsigned_option(*g_simp_max_steps, LEAN_DEFAULT_SIMP_MAX_STEPS,
                             "(simp tactic) maximum number of steps that can be performed by the simplifier");

    g_simp_trace = new name{"simp", "trace"};
    register_bool_option(*g_simp_trace, LEAN_DEFAULT_SIMP_TRACE,
                         "(simp tactic) if true the simplifier produces an execution trace for debugging purposes");

    g_simp_assumptions = new name{"simp", "assumptions"};
    register_bool_option(*g_simp_assumptions, LEAN_DEFAULT_SIMP_ASSUMPTIONS,
                         "(simp tactic) if true assumptions/hypotheses are automatically used as rewriting rules");

    g_simp_funext = new name{"simp", "funext"};
    register_bool_option(*g_simp_funext, LEAN_DEFAULT_SIMP_FUNEXT,
                         "(simp tactic) avoid function extensionality even if theorem/axiom is in the environment");

    g_simp_propext = new name{"simp", "propext"};
    register_bool_option(*g_simp_funext, LEAN_DEFAULT_SIMP_PROPEXT,
                         "(simp tactic) avoid proposition extensionality even if axiom is in the environment, this option is ignored in HoTT mode");
}

void finalize_simp_tactic() {
    delete g_simp_tactic;
    delete g_simp_single_pass;
    delete g_simp_bottom_up;
    delete g_simp_beta_eta;
    delete g_simp_iota;
    delete g_simp_memoize;
    delete g_simp_max_steps;
    delete g_simp_trace;
    delete g_simp_assumptions;
    delete g_simp_funext;
    delete g_simp_propext;
}
}
