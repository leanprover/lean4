/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/freset.h"
#include "util/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/normalizer.h"
#include "kernel/kernel.h"
#include "kernel/max_sharing.h"
#include "library/heq_decls.h"
#include "library/kernel_bindings.h"
#include "library/expr_pair.h"
#include "library/hop_match.h"
#include "library/expr_lt.h"
#include "library/simplifier/rewrite_rule_set.h"

#ifndef LEAN_SIMPLIFIER_PROOFS
#define LEAN_SIMPLIFIER_PROOFS true
#endif

#ifndef LEAN_SIMPLIFIER_CONTEXTUAL
#define LEAN_SIMPLIFIER_CONTEXTUAL true
#endif

#ifndef LEAN_SIMPLIFIER_SINGLE_PASS
#define LEAN_SIMPLIFIER_SINGLE_PASS false
#endif

#ifndef LEAN_SIMPLIFIER_BETA
#define LEAN_SIMPLIFIER_BETA true
#endif

#ifndef LEAN_SIMPLIFIER_ETA
#define LEAN_SIMPLIFIER_ETA true
#endif

#ifndef LEAN_SIMPLIFIER_EVAL
#define LEAN_SIMPLIFIER_EVAL true
#endif

#ifndef LEAN_SIMPLIFIER_UNFOLD
#define LEAN_SIMPLIFIER_UNFOLD false
#endif

#ifndef LEAN_SIMPLIFIER_CONDITIONAL
#define LEAN_SIMPLIFIER_CONDITIONAL true
#endif

#ifndef LEAN_SIMPLIFIER_MEMOIZE
#define LEAN_SIMPLIFIER_MEMOIZE true
#endif

#ifndef LEAN_SIMPLIFIER_MAX_STEPS
#define LEAN_SIMPLIFIER_MAX_STEPS std::numeric_limits<unsigned>::max()
#endif

namespace lean {
static name g_simplifier_proofs       {"simplifier", "proofs"};
static name g_simplifier_contextual   {"simplifier", "contextual"};
static name g_simplifier_single_pass  {"simplifier", "single_pass"};
static name g_simplifier_beta         {"simplifier", "beta"};
static name g_simplifier_eta          {"simplifier", "eta"};
static name g_simplifier_eval         {"simplifier", "eval"};
static name g_simplifier_unfold       {"simplifier", "unfold"};
static name g_simplifier_conditional  {"simplifier", "conditional"};
static name g_simplifier_memoize      {"simplifier", "memoize"};
static name g_simplifier_max_steps    {"simplifier", "max_steps"};

RegisterBoolOption(g_simplifier_proofs, LEAN_SIMPLIFIER_PROOFS, "(simplifier) generate proofs");
RegisterBoolOption(g_simplifier_contextual, LEAN_SIMPLIFIER_CONTEXTUAL, "(simplifier) contextual simplification");
RegisterBoolOption(g_simplifier_single_pass, LEAN_SIMPLIFIER_SINGLE_PASS, "(simplifier) if false then the simplifier keeps applying simplifications as long as possible");
RegisterBoolOption(g_simplifier_beta, LEAN_SIMPLIFIER_BETA, "(simplifier) use beta-reduction");
RegisterBoolOption(g_simplifier_eta, LEAN_SIMPLIFIER_ETA, "(simplifier) use eta-reduction");
RegisterBoolOption(g_simplifier_eval, LEAN_SIMPLIFIER_EVAL, "(simplifier) apply reductions based on computation");
RegisterBoolOption(g_simplifier_unfold, LEAN_SIMPLIFIER_UNFOLD, "(simplifier) unfolds non-opaque definitions");
RegisterBoolOption(g_simplifier_conditional, LEAN_SIMPLIFIER_CONDITIONAL, "(simplifier) conditional rewriting");
RegisterBoolOption(g_simplifier_memoize, LEAN_SIMPLIFIER_MEMOIZE, "(simplifier) memoize/cache intermediate results");
RegisterUnsignedOption(g_simplifier_max_steps, LEAN_SIMPLIFIER_MAX_STEPS, "(simplifier) maximum number of steps");

bool get_simplifier_proofs(options const & opts) {
    return opts.get_bool(g_simplifier_proofs, LEAN_SIMPLIFIER_PROOFS);
}
bool get_simplifier_contextual(options const & opts) {
    return opts.get_bool(g_simplifier_contextual, LEAN_SIMPLIFIER_CONTEXTUAL);
}
bool get_simplifier_single_pass(options const & opts) {
    return opts.get_bool(g_simplifier_single_pass, LEAN_SIMPLIFIER_SINGLE_PASS);
}
bool get_simplifier_beta(options const & opts) {
    return opts.get_bool(g_simplifier_beta, LEAN_SIMPLIFIER_BETA);
}
bool get_simplifier_eta(options const & opts) {
    return opts.get_bool(g_simplifier_eta, LEAN_SIMPLIFIER_ETA);
}
bool get_simplifier_eval(options const & opts) {
    return opts.get_bool(g_simplifier_eval, LEAN_SIMPLIFIER_EVAL);
}
bool get_simplifier_unfold(options const & opts) {
    return opts.get_bool(g_simplifier_unfold, LEAN_SIMPLIFIER_UNFOLD);
}
bool get_simplifier_conditional(options const & opts) {
    return opts.get_bool(g_simplifier_conditional, LEAN_SIMPLIFIER_CONDITIONAL);
}
bool get_simplifier_memoize(options const & opts) {
    return opts.get_bool(g_simplifier_memoize, LEAN_SIMPLIFIER_MEMOIZE);
}
unsigned get_simplifier_max_steps(options const & opts) {
    return opts.get_unsigned(g_simplifier_max_steps, LEAN_SIMPLIFIER_MAX_STEPS);
}

class simplifier_fn {
    struct result {
        expr           m_out;    // the result of a simplification step
        optional<expr> m_proof;  // a proof that the result is equal to the input (when m_proofs_enabled)
        bool           m_heq_proof; // true if the proof is for heterogeneous equality
        explicit result(expr const & out, bool heq_proof = false):
            m_out(out), m_heq_proof(heq_proof) {}
        result(expr const & out, expr const & pr, bool heq_proof = false):
            m_out(out), m_proof(pr), m_heq_proof(heq_proof) {}
        result(expr const & out, optional<expr> const & pr, bool heq_proof = false):
            m_out(out), m_proof(pr), m_heq_proof(heq_proof) {}
    };

    typedef std::vector<rewrite_rule_set> rule_sets;
    typedef expr_map<result> cache;
    ro_environment m_env;
    type_checker   m_tc;
    bool           m_has_heq;
    context        m_ctx;
    rule_sets      m_rule_sets;
    cache          m_cache;
    max_sharing_fn m_max_sharing;

    unsigned       m_num_steps; // number of steps performed

    // Configuration
    bool           m_proofs_enabled;
    bool           m_contextual;
    bool           m_single_pass;
    bool           m_beta;
    bool           m_eta;
    bool           m_eval;
    bool           m_unfold;
    bool           m_conditional;
    bool           m_memoize;
    unsigned       m_max_steps;

    struct set_context {
        flet<context> m_set;
        freset<cache> m_reset_cache;
        set_context(simplifier_fn & s, context const & new_ctx):m_set(s.m_ctx, new_ctx), m_reset_cache(s.m_cache) {}
    };

    /**
       \brief Return a lambda with body \c new_body, and name and domain from abst.
    */
    static expr mk_lambda(expr const & abst, expr const & new_body) {
        return ::lean::mk_lambda(abst_name(abst), abst_domain(abst), new_body);
    }

    bool is_proposition(expr const & e) {
        return m_tc.is_proposition(e, m_ctx);
    }

    expr infer_type(expr const & e) {
        return m_tc.infer_type(e, m_ctx);
    }

    expr ensure_pi(expr const & e) {
        return m_tc.ensure_pi(e, m_ctx);
    }

    expr normalize(expr const & e) {
        normalizer & proc = m_tc.get_normalizer();
        return proc(e, m_ctx, true);
    }

    expr mk_congr1_th(expr const & f_type, expr const & f, expr const & new_f, expr const & a, expr const & Heq_f) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        return ::lean::mk_congr1_th(A, B, f, new_f, a, Heq_f);
    }

    expr mk_congr2_th(expr const & f_type, expr const & a, expr const & new_a, expr const & f, expr const & Heq_a) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        return ::lean::mk_congr2_th(A, B, a, new_a, f, Heq_a);
    }

    expr mk_congr_th(expr const & f_type, expr const & f, expr const & new_f, expr const & a, expr const & new_a,
                     expr const & Heq_f, expr const & Heq_a) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        return ::lean::mk_congr_th(A, B, f, new_f, a, new_a, Heq_f, Heq_a);
    }

    expr mk_hcongr_th(expr const & f_type, expr const & new_f_type, expr const & f, expr const & new_f,
                      expr const & a, expr const & new_a, expr const & Heq_f, expr const & Heq_a) {
        return ::lean::mk_hcongr_th(abst_domain(f_type),
                                    abst_domain(new_f_type),
                                    mk_lambda(f_type, abst_body(f_type)),
                                    mk_lambda(new_f_type, abst_body(new_f_type)),
                                    f, new_f, a, new_a, Heq_f, Heq_a);
    }

    /**
       \brief Given
                a           = b_res.m_out  with proof b_res.m_proof
                b_res.m_out = c            with proof H_bc
       This method returns a new result r s.t. r.m_out == c and a proof of a = c
    */
    result mk_trans_result(expr const & a, result const & b_res, expr const & c, expr const & H_bc) {
        if (m_proofs_enabled) {
            if (!b_res.m_proof) {
                // The proof of a = b is reflexivity
                return result(c, H_bc);
            } else {
                expr const & b = b_res.m_out;
                expr new_proof;
                bool heq_proof = false;
                if (b_res.m_heq_proof) {
                    expr b_type = infer_type(b);
                    new_proof = ::lean::mk_htrans_th(infer_type(a), b_type, b_type, /* b and c must have the same type */
                                                     a, b, c, *b_res.m_proof, mk_to_heq_th(b_type, b, c, H_bc));
                    heq_proof = true;
                } else {
                    new_proof = ::lean::mk_trans_th(infer_type(a), a, b, c, *b_res.m_proof, H_bc);
                }
                return result(c, new_proof, heq_proof);
            }
        } else {
            return result(c);
        }
    }

    /**
       \brief Given
                a           = b_res.m_out    with proof b_res.m_proof
                b_res.m_out = c_res.m_out    with proof c_res.m_proof

       This method returns a new result r s.t. r.m_out == c and a proof of a = c_res.m_out
    */
    result mk_trans_result(expr const & a, result const & b_res, result const & c_res) {
        if (m_proofs_enabled) {
            if (!b_res.m_proof) {
                // the proof of a == b is reflexivity
                return c_res;
            } else if (!c_res.m_proof) {
                // the proof of b == c is reflexivity
                return result(c_res.m_out, *b_res.m_proof, b_res.m_heq_proof);
            } else {
                bool heq_proof = b_res.m_heq_proof || c_res.m_heq_proof;
                expr new_proof;
                expr const & b = b_res.m_out;
                expr const & c = c_res.m_out;
                if (heq_proof) {
                    expr a_type = infer_type(a);
                    expr b_type = infer_type(b);
                    expr c_type = infer_type(c);
                    expr H_ab   = *b_res.m_proof;
                    if (!b_res.m_heq_proof)
                        H_ab = mk_to_heq_th(a_type, a, b, H_ab);
                    expr H_bc   = *c_res.m_proof;
                    if (!c_res.m_heq_proof)
                        H_bc = mk_to_heq_th(b_type, b, c, H_bc);
                    new_proof = ::lean::mk_htrans_th(a_type, b_type, c_type, a, b, c, H_ab, H_bc);
                } else {
                    new_proof = ::lean::mk_trans_th(infer_type(a), a, b, c, *b_res.m_proof, *c_res.m_proof);
                }
                return result(c, new_proof, heq_proof);
            }
        } else {
            // proof generation is disabled
            return c_res;
        }
    }

    expr mk_app_prefix(unsigned i, expr const & a) {
        lean_assert(i > 0);
        if (i == 1)
            return arg(a, 0);
        else
            return mk_app(i, &arg(a, 0));
    }

    expr mk_app_prefix(unsigned i, buffer<expr> const & args) {
        lean_assert(i > 0);
        if (i == 1)
            return args[0];
        else
            return mk_app(i, args.data());
    }

    result simplify_app(expr const & e) {
        lean_assert(is_app(e));
        buffer<expr>           new_args;
        buffer<optional<expr>> proofs;               // used only if m_proofs_enabled
        buffer<expr>           f_types, new_f_types; // used only if m_proofs_enabled
        buffer<bool>           heq_proofs;           // used only if m_has_heq && m_proofs_enabled
        bool changed = false;
        expr f       = arg(e, 0);
        expr f_type  = infer_type(f);
        result res_f = simplify(f);
        expr new_f   = res_f.m_out;
        expr new_f_type;
        if (new_f != f)
            changed = true;
        new_args.push_back(new_f);
        if (m_proofs_enabled) {
            proofs.push_back(res_f.m_proof);
            f_types.push_back(f_type);
            new_f_type = res_f.m_heq_proof ? infer_type(new_f) : f_type;
            new_f_types.push_back(new_f_type);
            if (m_has_heq)
                heq_proofs.push_back(res_f.m_heq_proof);
        }
        unsigned num = num_args(e);
        for (unsigned i = 1; i < num; i++) {
            f_type = ensure_pi(f_type);
            bool f_arrow   = is_arrow(f_type);
            expr const & a = arg(e, i);
            result res_a(a);
            if (m_has_heq || f_arrow) {
                res_a = simplify(a);
                if (res_a.m_out != a)
                    changed = true;
            }
            expr new_a = res_a.m_out;
            new_args.push_back(new_a);
            if (m_proofs_enabled) {
                proofs.push_back(res_a.m_proof);
                if (m_has_heq)
                    heq_proofs.push_back(res_a.m_heq_proof);
                bool changed_f_type = !is_eqp(f_type, new_f_type);
                if (f_arrow) {
                    f_type     = lower_free_vars(abst_body(f_type), 1, 1);
                    new_f_type = changed_f_type ? lower_free_vars(abst_body(new_f_type), 1, 1) : f_type;
                } else if (is_eqp(a, new_a)) {
                    f_type     = pi_body_at(f_type, a);
                    new_f_type = changed_f_type ? pi_body_at(new_f_type, a) : f_type;
                } else {
                    f_type     = pi_body_at(f_type, a);
                    new_f_type = pi_body_at(new_f_type, new_a);
                }
                f_types.push_back(f_type);
                new_f_types.push_back(new_f_type);
            }
        }

        if (!changed) {
            return rewrite_app(e, result(e));
        } else if (!m_proofs_enabled) {
            return rewrite_app(e, result(mk_app(new_args)));
        } else {
            expr out = mk_app(new_args);
            unsigned i = 0;
            while (i < num && !proofs[i]) {
                // skip "reflexive" proofs
                i++;
            }
            if (i == num)
                return rewrite_app(e, result(out));
            expr pr;
            bool heq_proof = false;
            if (i == 0) {
                pr = *(proofs[0]);
                heq_proof = m_has_heq && heq_proofs[0];
            } else if (m_has_heq && heq_proofs[i]) {
                expr f = mk_app_prefix(i, new_args);
                pr = mk_hcongr_th(f_types[i-1], f_types[i-1], f, f, arg(e, i), new_args[i],
                                  mk_hrefl_th(f_types[i-1], f), *(proofs[i]));
                heq_proof = true;
            } else {
                expr f = mk_app_prefix(i, new_args);
                pr = mk_congr2_th(f_types[i-1], arg(e, i), new_args[i], f, *(proofs[i]));
            }
            i++;
            for (; i < num; i++) {
                expr f     = mk_app_prefix(i, e);
                expr new_f = mk_app_prefix(i, new_args);
                if (proofs[i]) {
                    if (m_has_heq && heq_proofs[i]) {
                        if (!heq_proof)
                            pr = mk_to_heq_th(f_types[i], f, new_f, pr);
                        pr = mk_hcongr_th(f_types[i-1], new_f_types[i-1], f, new_f, arg(e, i), new_args[i], pr, *(proofs[i]));
                        heq_proof = true;
                    } else {
                        pr = mk_congr_th(f_types[i-1], f, new_f, arg(e, i), new_args[i], pr, *(proofs[i]));
                    }
                } else if (heq_proof) {
                    pr = mk_hcongr_th(f_types[i-1], new_f_types[i-1], f, new_f, arg(e, i), arg(e, i),
                                      pr, mk_hrefl_th(abst_domain(f_types[i-1]), arg(e, i)));
                } else {
                    lean_assert(!heq_proof);
                    pr = mk_congr1_th(f_types[i-1], f, new_f, arg(e, i), pr);
                }
            }
            return rewrite_app(e, result(out, pr, heq_proof));
        }
    }

    /** \brief Return true when \c e is a value from the point of view of the simplifier */
    static bool is_value(expr const & e) {
        // Currently only semantic attachments are treated as value.
        // We may relax that in the future.
        return ::lean::is_value(e);
    }

    /**
       \brief Return true iff the simplifier should use the evaluator/normalizer to reduce application
    */
    bool evaluate_app(expr const & e) const {
        lean_assert(is_app(e));
        // only evaluate if it is enabled
        if (!m_eval)
            return false;
        // if all arguments are values, we should evaluate
        if (std::all_of(args(e).begin()+1, args(e).end(), [](expr const & a) { return is_value(a); }))
            return true;
        // The previous test fails for equality/disequality because the first arguments are types.
        // Should we have something more general for cases like that?
        // Some possibilities:
        //   - We have a table mapping constants to argument positions. The positions tell the simplifier
        //     which arguments must be value to trigger evaluation.
        //   - We have an external predicate that is invoked by the simplifier to decide whether to normalize/evaluate an
        //     expression.
        unsigned num = num_args(e);
        return
            (is_eq(e) || is_neq(e) || is_heq(e)) &&
            is_value(arg(e, num-2)) &&
            is_value(arg(e, num-1));
    }

    /**
       \brief Given (applications) lhs and rhs s.t. lhs = rhs.m_out
       with proof rhs.m_proof, this method applies rewrite rules, beta
       and evaluation to \c rhs.m_out, and return a new result object
       new_rhs s.t.  lhs = new_rhs.m_out with proof new_rhs.m_proof

       \pre is_app(lhs)
       \pre is_app(rhs.m_out)
    */
    result rewrite_app(expr const & lhs, result const & rhs) {
        lean_assert(is_app(rhs.m_out));
        lean_assert(is_app(lhs));
        if (evaluate_app(rhs.m_out)) {
            // try to evaluate if all arguments are values.
            expr new_rhs = normalize(rhs.m_out);
            if (is_value(new_rhs)) {
                // We don't need to create a new proof term since rhs.m_out and new_rhs are
                // definitionally equal.
                return rewrite(lhs, result(new_rhs, rhs.m_proof, rhs.m_heq_proof));
            }
        }

        expr f   = arg(rhs.m_out, 0);
        if (m_beta && is_lambda(f)) {
            expr new_rhs = head_beta_reduce(rhs.m_out);
            // rhs.m_out and new_rhs are also definitionally equal
            return rewrite(lhs, result(new_rhs, rhs.m_proof, rhs.m_heq_proof));
        }

        return rewrite(lhs, rhs);
    }


    bool found_all_args(unsigned num, buffer<optional<expr>> const & subst, buffer<expr> & new_args) {
        for (unsigned i = 0; i < num; i++) {
            if (!subst[i])
                return false;
            new_args[i+1] = *subst[i];
        }
        return true;
    }

    /**
       \brief Given lhs and rhs s.t. lhs = rhs.m_out with proof rhs.m_proof,
       this method applies rewrite rules, beta and evaluation to \c rhs.m_out,
       and return a new result object new_rhs s.t.
                lhs = new_rhs.m_out
       with proof new_rhs.m_proof
    */
    result rewrite(expr const & lhs, result const & rhs) {
        expr target = rhs.m_out;
        buffer<optional<expr>> subst;
        buffer<expr>           new_args;
        expr                   new_rhs;
        expr                   new_proof;
        auto check_rule_fn = [&](rewrite_rule const & rule) -> bool {
            unsigned num = rule.get_num_args();
            subst.clear();
            subst.resize(num);
            if (hop_match(rule.get_lhs(), target, subst, optional<ro_environment>(m_env))) {
                new_args.clear();
                new_args.resize(num+1);
                if (found_all_args(num, subst, new_args)) {
                    // easy case: all arguments found
                    new_rhs   = instantiate(rule.get_rhs(), num, new_args.data() + 1);
                    if (rule.is_permutation() && !is_lt(new_rhs, target, false))
                        return false;
                    if (m_proofs_enabled) {
                        if (num > 0) {
                            new_args[0] = rule.get_proof();
                            new_proof   = mk_app(new_args);
                        } else {
                            new_proof   = rule.get_proof();
                        }
                    }
                    return true;
                } else {
                    // Conditional rewriting: we try to fill the missing
                    // arguments by trying to find a proof for ones that are
                    // propositions.
                    expr ceq = rule.get_ceq();
                    buffer<expr> & proof_args = new_args;
                    proof_args.clear();
                    if (m_proofs_enabled)
                        proof_args.push_back(rule.get_proof());
                    for (unsigned i = 0; i < num; i++) {
                        lean_assert(is_pi(ceq));
                        if (subst[i]) {
                            ceq = instantiate(abst_body(ceq), *subst[i]);
                            if (m_proofs_enabled)
                                proof_args.push_back(*subst[i]);
                        } else {
                            expr d = abst_domain(ceq);
                            if (is_proposition(d)) {
                                result d_res = simplify(d);
                                if (d_res.m_out == True) {
                                    if (m_proofs_enabled) {
                                        expr d_proof;
                                        if (!d_res.m_proof) {
                                            // No proof available. So d should be definitionally equal to True
                                            d_proof = mk_trivial();
                                        } else {
                                            d_proof = mk_eqt_elim_th(d, *d_res.m_proof);
                                        }
                                        ceq = instantiate(abst_body(ceq), d_proof);
                                        proof_args.push_back(d_proof);
                                    } else if (is_arrow(ceq)) {
                                        ceq = lower_free_vars(abst_body(ceq), 1, 1);
                                    } else {
                                        // The body of ceq depends on this argument,
                                        // but proof generation is not enabled.
                                        // So, we should fail
                                        return false;
                                    }
                                } else {
                                    // failed to prove proposition
                                    return false;
                                }
                            } else {
                                // failed, the argument is not a proposition
                                return false;
                            }
                        }
                    }
                    new_proof = mk_app(proof_args);
                    new_rhs   = arg(ceq, num_args(ceq) - 1);
                    if (rule.is_permutation() && !is_lt(new_rhs, target, false))
                        return false;
                    return true;
                }
            }
            return false;
        };
        // Traverse all rule sets
        for (rewrite_rule_set const & rs : m_rule_sets) {
            if (rs.find_match(target, check_rule_fn)) {
                // the result is in new_rhs and proof at new_proof
                result new_r1 = mk_trans_result(lhs, rhs, new_rhs, new_proof);
                if (m_single_pass) {
                    return new_r1;
                } else {
                    result new_r2 = simplify(new_r1.m_out);
                    return mk_trans_result(lhs, new_r1, new_r2);
                }
            }
        }
        if (!m_single_pass && lhs != rhs.m_out) {
            result new_rhs = simplify(rhs.m_out);
            return mk_trans_result(lhs, rhs, new_rhs);
        } else {
            return rhs;
        }
    }

    result simplify_var(expr const & e) {
        if (m_has_heq) {
            // TODO(Leo)
            return result(e);
        } else {
            return result(e);
        }
    }

    result simplify_constant(expr const & e) {
        lean_assert(is_constant(e));
        if (m_unfold || m_eval) {
            auto obj = m_env->find_object(const_name(e));
            if (m_unfold && should_unfold(obj)) {
                expr e = obj->get_value();
                if (m_single_pass) {
                    return result(e);
                } else {
                    return simplify(e);
                }
            }
            if (m_eval && obj->is_builtin()) {
                return result(obj->get_value());
            }
        }
        return rewrite(e, result(e));
    }

    /**
       \brief Return true iff Eta-reduction can be applied to \c e.

       \remark Actually this is a partial test. Given,
                  fun x : T, f x
       This method does not check whether f has type
                   Pi x : T, B x
       This check must be performed in the caller.
       Otherwise the proof (eta T (fun x : T, B x) f) will not type check.
    */
    bool is_eta_target(expr const & e) const {
        if (is_lambda(e)) {
            expr b = abst_body(e);
            return
                is_app(b) && is_var(arg(b, num_args(b) - 1), 0) &&
                std::all_of(begin_args(b), end_args(b) - 1, [](expr const & a) { return !has_free_var(a, 0); });
        } else {
            return false;
        }
    }

    /**
       \brief Given (lambdas) lhs and rhs s.t. lhs = rhs.m_out
       with proof rhs.m_proof, this method applies rewrite rules, and
       eta reduction, and return a new result object new_rhs s.t.
              lhs = new_rhs.m_out with proof new_rhs.m_proof

       \pre is_lambda(lhs)
       \pre is_lambda(rhs.m_out)
    */
    result rewrite_lambda(expr const & lhs, result const & rhs) {
        lean_assert(is_lambda(lhs));
        lean_assert(is_lambda(rhs.m_out));
        if (m_eta && is_eta_target(rhs.m_out)) {
            expr b = abst_body(rhs.m_out);
            expr new_rhs;
            if (num_args(b) > 2) {
                new_rhs = mk_app(num_args(b) - 1, &arg(b, 0));
            } else {
                new_rhs = arg(b, 0);
            }
            new_rhs           = lower_free_vars(new_rhs, 1, 1);
            expr new_rhs_type = ensure_pi(infer_type(new_rhs));
            if (m_tc.is_eq_convertible(abst_domain(new_rhs_type), abst_domain(rhs.m_out), m_ctx)) {
                if (m_proofs_enabled) {
                    expr new_proof = mk_eta_th(abst_domain(rhs.m_out),
                                               mk_lambda(rhs.m_out, abst_body(new_rhs_type)),
                                               new_rhs);
                    return rewrite(lhs, mk_trans_result(lhs, rhs, new_rhs, new_proof));
                } else {
                    return rewrite(lhs, result(new_rhs));
                }
            }
        }
        return rewrite(lhs, rhs);
    }

    result simplify_lambda(expr const & e) {
        lean_assert(is_lambda(e));
        if (m_has_heq) {
            // TODO(Leo)
            return result(e);
        } else {
            set_context set(*this, extend(m_ctx, abst_name(e), abst_domain(e)));
            result res_body = simplify(abst_body(e));
            lean_assert(!res_body.m_heq_proof);
            expr new_body = res_body.m_out;
            if (is_eqp(new_body, abst_body(e)))
                return rewrite_lambda(e, result(e));
            expr out = mk_lambda(e, new_body);
            if (!m_proofs_enabled || !res_body.m_proof)
                return rewrite_lambda(e, result(out));
            expr body_type = infer_type(abst_body(e));
            expr pr  = mk_funext_th(abst_domain(e), mk_lambda(e, body_type), e, out,
                                    mk_lambda(e, *res_body.m_proof));
            return rewrite_lambda(e, result(out, pr));
        }
    }

    result simplify_pi(expr const & e) {
        lean_assert(is_pi(e));
        // TODO(Leo): handle implication, i.e., e is_proposition and is_arrow
        if (m_has_heq) {
            // TODO(Leo)
            return result(e);
        } else if (is_proposition(e)) {
            set_context set(*this, extend(m_ctx, abst_name(e), abst_domain(e)));
            result res_body = simplify(abst_body(e));
            lean_assert(!res_body.m_heq_proof);
            expr new_body = res_body.m_out;
            if (is_eqp(new_body, abst_body(e)))
                return rewrite(e, result(e));
            expr out = mk_pi(abst_name(e), abst_domain(e), new_body);
            if (!m_proofs_enabled || !res_body.m_proof)
                return rewrite(e, result(out));
            expr pr  = mk_allext_th(abst_domain(e),
                                    mk_lambda(e, abst_body(e)),
                                    mk_lambda(e, abst_body(out)),
                                    mk_lambda(e, *res_body.m_proof));
            return rewrite(e, result(out, pr));
        } else {
            // if the environment does not contain heq axioms, then we don't simplify Pi's that are not forall's
            return result(e);
        }
    }

    result save(expr const & e, result const & r) {
        if (m_memoize) {
            result new_r(m_max_sharing(r.m_out), r.m_proof, r.m_heq_proof);
            m_cache.insert(mk_pair(e, new_r));
            return new_r;
        } else {
            return r;
        }
    }

    result simplify(expr e) {
        check_system("simplifier");
        m_num_steps++;
        if (m_num_steps > m_max_steps)
            throw exception("simplifier failed, maximum number of steps exceeded");
        if (m_memoize) {
            e = m_max_sharing(e);
            auto it = m_cache.find(e);
            if (it != m_cache.end()) {
                return it->second;
            }
        }
        switch (e.kind()) {
        case expr_kind::Var:      return save(e, simplify_var(e));
        case expr_kind::Constant: return save(e, simplify_constant(e));
        case expr_kind::Type:
        case expr_kind::MetaVar:
        case expr_kind::Value:    return save(e, result(e));
        case expr_kind::App:      return save(e, simplify_app(e));
        case expr_kind::Lambda:   return save(e, simplify_lambda(e));
        case expr_kind::Pi:       return save(e, simplify_pi(e));
        case expr_kind::Let:      return save(e, simplify(instantiate(let_body(e), let_value(e))));
        }
        lean_unreachable();
    }

    void set_options(options const & o) {
        m_proofs_enabled = get_simplifier_proofs(o);
        m_contextual     = get_simplifier_contextual(o);
        m_single_pass    = get_simplifier_single_pass(o);
        m_beta           = get_simplifier_beta(o);
        m_eta            = get_simplifier_eta(o);
        m_eval           = get_simplifier_eval(o);
        m_unfold         = get_simplifier_unfold(o);
        m_conditional    = get_simplifier_conditional(o);
        m_memoize        = get_simplifier_memoize(o);
        m_max_steps      = get_simplifier_max_steps(o);
    }

public:
    simplifier_fn(ro_environment const & env, options const & o, unsigned num_rs, rewrite_rule_set const * rs):
        m_env(env), m_tc(env), m_rule_sets(rs, rs + num_rs) {
        m_has_heq = m_env->imported("heq");
        set_options(o);
    }

    expr_pair operator()(expr const & e, context const & ctx) {
        set_context set(*this, ctx);
        m_num_steps = 0;
        auto r = simplify(e);
        if (r.m_proof) {
            return mk_pair(r.m_out, *(r.m_proof));
        } else {
            return mk_pair(r.m_out, mk_refl_th(infer_type(r.m_out), r.m_out));
        }
    }
};

expr_pair simplify(expr const & e, ro_environment const & env, context const & ctx, options const & opts,
                   unsigned num_rs, rewrite_rule_set const * rs) {
    return simplifier_fn(env, opts, num_rs, rs)(e, ctx);
}

expr_pair simplify(expr const & e, ro_environment const & env, context const & ctx, options const & opts,
                   unsigned num_ns, name const * ns) {
    buffer<rewrite_rule_set> rules;
    for (unsigned i = 0; i < num_ns; i++)
        rules.push_back(get_rewrite_rule_set(env, ns[i]));
    return simplify(e, env, ctx, opts, num_ns, rules.data());
}

static int simplify_core(lua_State * L, ro_shared_environment const & env) {
    int nargs = lua_gettop(L);
    expr const & e = to_expr(L, 1);
    buffer<rewrite_rule_set> rules;
    if (nargs == 1) {
        rules.push_back(get_rewrite_rule_set(env));
    } else {
        if (lua_isstring(L, 2)) {
            rules.push_back(get_rewrite_rule_set(env, to_name_ext(L, 2)));
        } else {
            luaL_checktype(L, 2, LUA_TTABLE);
            name r;
            int n = objlen(L, 2);
            for (int i = 1; i <= n; i++) {
                lua_rawgeti(L, 2, i);
                rules.push_back(get_rewrite_rule_set(env, to_name_ext(L, -1)));
                lua_pop(L, 1);
            }
        }
    }
    context ctx;
    options opts;
    if (nargs >= 4)
        ctx = to_context(L, 4);
    if (nargs >= 5)
        opts = to_options(L, 5);
    auto r = simplify(e, env, ctx, opts, rules.size(), rules.data());
    push_expr(L, r.first);
    push_expr(L, r.second);
    return 2;
}

static int simplify(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs <= 2)
        return simplify_core(L, ro_shared_environment(L));
    else
        return simplify_core(L, ro_shared_environment(L, 3));
}

void open_simplifier(lua_State * L) {
    SET_GLOBAL_FUN(simplify, "simplify");
}
}
