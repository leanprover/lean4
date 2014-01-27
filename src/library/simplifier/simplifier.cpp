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
#include "kernel/abstract.h"
#include "kernel/normalizer.h"
#include "kernel/kernel.h"
#include "kernel/max_sharing.h"
#include "kernel/occurs.h"
#include "library/heq_decls.h"
#include "library/cast_decls.h"
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

bool get_simplifier_proofs(options const & opts) { return opts.get_bool(g_simplifier_proofs, LEAN_SIMPLIFIER_PROOFS); }
bool get_simplifier_contextual(options const & opts) { return opts.get_bool(g_simplifier_contextual, LEAN_SIMPLIFIER_CONTEXTUAL); }
bool get_simplifier_single_pass(options const & opts) { return opts.get_bool(g_simplifier_single_pass, LEAN_SIMPLIFIER_SINGLE_PASS); }
bool get_simplifier_beta(options const & opts) { return opts.get_bool(g_simplifier_beta, LEAN_SIMPLIFIER_BETA); }
bool get_simplifier_eta(options const & opts) { return opts.get_bool(g_simplifier_eta, LEAN_SIMPLIFIER_ETA); }
bool get_simplifier_eval(options const & opts) { return opts.get_bool(g_simplifier_eval, LEAN_SIMPLIFIER_EVAL); }
bool get_simplifier_unfold(options const & opts) { return opts.get_bool(g_simplifier_unfold, LEAN_SIMPLIFIER_UNFOLD); }
bool get_simplifier_conditional(options const & opts) { return opts.get_bool(g_simplifier_conditional, LEAN_SIMPLIFIER_CONDITIONAL); }
bool get_simplifier_memoize(options const & opts) { return opts.get_bool(g_simplifier_memoize, LEAN_SIMPLIFIER_MEMOIZE); }
unsigned get_simplifier_max_steps(options const & opts) { return opts.get_unsigned(g_simplifier_max_steps, LEAN_SIMPLIFIER_MAX_STEPS); }

static name g_local("local");
static name g_C("C");
static name g_H("H");
static name g_x("x");
static name g_unique = name::mk_internal_unique_name();

class simplifier_fn {
    struct result {
        expr           m_expr;      // the result of a simplification step
        optional<expr> m_proof;     // a proof that the result is equal to the input (when m_proofs_enabled)
        bool           m_heq_proof; // true if the proof has type lhs == rhs (i.e., it is a heterogeneous equality)
        result() {}
        explicit result(expr const & out, bool heq_proof = false):
            m_expr(out), m_heq_proof(heq_proof) {}
        result(expr const & out, expr const & pr, bool heq_proof = false):
            m_expr(out), m_proof(pr), m_heq_proof(heq_proof) {}
        result(expr const & out, optional<expr> const & pr, bool heq_proof = false):
            m_expr(out), m_proof(pr), m_heq_proof(heq_proof) {}
        bool is_heq_proof() const { return m_heq_proof; }
        result update_expr(expr const & new_e) const { return result(new_e, m_proof, m_heq_proof); }
    };

    typedef std::vector<rewrite_rule_set> rule_sets;
    typedef expr_map<result> cache;
    typedef std::vector<congr_theorem_info const *> congr_thms;
    typedef cache const_map;
    ro_environment m_env;
    type_checker   m_tc;
    bool           m_has_heq;
    bool           m_has_cast;
    context        m_ctx;
    rule_sets      m_rule_sets;
    cache          m_cache;
    max_sharing_fn m_max_sharing;
    const_map      m_const_map;  // mapping from old to new constants in hfunext and hpiext
    congr_thms     m_congr_thms;
    unsigned       m_next_idx;  // index used to create fresh constants
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

    struct updt_rule_set {
        simplifier_fn &    m_fn;
        rewrite_rule_set   m_old;
        freset<cache>      m_reset_cache; // must reset the cache whenever we update the rule set.
        /**
           \brief Update the rule set using a constant H : P, where P is a proposition.

           \pre const_type(H)
        */
        updt_rule_set(simplifier_fn & fn, expr const & H):
            m_fn(fn), m_old(m_fn.m_rule_sets[0]), m_reset_cache(m_fn.m_cache) {
            lean_assert(const_type(H));
            m_fn.m_rule_sets[0].insert(g_local, *const_type(H), H);
        }
        ~updt_rule_set() {
            m_fn.m_rule_sets[0] = m_old;
            // Remark: m_reset_cache destructor will restore the cache
        }
    };

    struct updt_const_map {
        simplifier_fn &    m_fn;
        expr const &       m_old_x;
        updt_const_map(simplifier_fn & fn, expr const & old_x, expr const & new_x, expr const & H):
            m_fn(fn), m_old_x(old_x) {
            m_fn.m_const_map[old_x] = result(new_x, H, true);
        }
        ~updt_const_map() {
            m_fn.m_const_map.erase(m_old_x);
        }
    };

    static expr mk_lambda(name const & n, expr const & d, expr const & b) {
        return ::lean::mk_lambda(n, d, b);
    }

    /**
       \brief Return a lambda with body \c new_body, and name and domain from abst.
    */
    static expr mk_lambda(expr const & abst, expr const & new_body) {
        return mk_lambda(abst_name(abst), abst_domain(abst), new_body);
    }

    bool is_proposition(expr const & e) {
        return m_tc.is_proposition(e, m_ctx);
    }

    bool is_convertible(expr const & t1, expr const & t2) {
        return m_tc.is_convertible(t1, t2, m_ctx);
    }

    bool is_definitionally_equal(expr const & t1, expr const & t2) {
        return m_tc.is_definitionally_equal(t1, t2, m_ctx);
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

    expr mk_fresh_const(expr const & type) {
        m_next_idx++;
        return mk_constant(name(g_unique, m_next_idx), type);
    }

    /**
       \brief Auxiliary method for converting a proof H of (@eq A a b) into (@eq B a b) when
       type A is convertible to B, but not definitionally equal.
    */
    expr translate_eq_proof(expr const & A, expr const & a, expr const & b, expr const & H, expr const & B) {
        if (A != B) {
            return mk_subst_th(A, a, b, mk_lambda(g_x, A, mk_eq(B, a, mk_var(0))), mk_refl_th(B, a), H);
        } else {
            return H;
        }
    }

    expr translate_eq_typem_proof(expr const & a, result const & b) {
        return translate_eq_proof(infer_type(a), a, b.m_expr, get_proof(b), mk_TypeM());
    }

    expr mk_congr1_th(expr const & f_type, expr const & f, expr const & new_f, expr const & a, expr const & Heq_f) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        return ::lean::mk_congr1_th(A, B, f, new_f, a, Heq_f);
    }

    expr mk_congr2_th(expr const & f_type, expr const & a, expr const & new_a, expr const & f, expr Heq_a) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        expr a_type = infer_type(a);
        if (!is_definitionally_equal(A, a_type))
            Heq_a = translate_eq_proof(a_type, a, new_a, Heq_a, A);
        return ::lean::mk_congr2_th(A, B, a, new_a, f, Heq_a);
    }

    expr mk_congr_th(expr const & f_type, expr const & f, expr const & new_f, expr const & a, expr const & new_a,
                     expr const & Heq_f, expr Heq_a) {
        expr const & A = abst_domain(f_type);
        expr B = lower_free_vars(abst_body(f_type), 1, 1);
        expr a_type = infer_type(a);
        if (!is_definitionally_equal(A, a_type))
            Heq_a = translate_eq_proof(a_type, a, new_a, Heq_a, A);
        return ::lean::mk_congr_th(A, B, f, new_f, a, new_a, Heq_f, Heq_a);
    }

    expr get_proof(result const & rhs) {
        if (rhs.m_proof) {
            return *rhs.m_proof;
        } else {
            // lhs and rhs are definitionally equal
            return mk_refl_th(infer_type(rhs.m_expr), rhs.m_expr);
        }
    }

    /**
       \brief Return true if \c e is definitionally equal to (Type U)

       This is an approximated solution. It may return false for cases where \c e
       is definitionally to TypeU.
    */
    bool is_TypeU(expr const & e) {
        if (is_type(e)) {
            return e == TypeU;
        } else if (is_constant(e)) {
            auto obj = m_env->find_object(const_name(e));
            return obj && obj->is_definition() && is_TypeU(obj->get_value());
        } else {
            return false;
        }
    }

    /**
       \brief Create heterogeneous congruence proof.
    */
    optional<expr> mk_hcongr_th(expr const & f_type, expr const & new_f_type, expr const & f, expr const & new_f,
                                expr const & Heq_f, expr const & a, result const & new_a) {
        expr const & A     = abst_domain(f_type);
        if (is_TypeU(A)) {
            if (!is_definitionally_equal(f, new_f))
                return none_expr(); // can't handle
            // The congruence axiom cannot be used in this case.
            // Type problem is that we would need provide a proof of (@eq (Type U) a new_a.m_expr),
            // and (Type U) has type (Type U+1) the congruence axioms expect arguments from
            // (Type U). We address this issue by using the following trick:
            //
            // We have
            //      f  : Pi x : (Type U), B x
            //      a  : (Type i)               s.t. U > i
            //      a' : (Type i)               where a' := new_a.m_expr
            //      H  : a = a'                 where H  := new_a.m_proof
            //
            // Then a proof term for (@heq (B a) (B a') (f a) (f a')) is
            //
            //    @subst (Type i) a a' (fun x : (Type i), (@heq (B a) (B x) (f a) (f x))) (@hrefl (B a) (f a)) H
            expr a_type   = infer_type(a);
            if (!is_convertible(a_type, A))
                return none_expr(); // can't handle
            expr a_prime  = new_a.m_expr;
            expr H        = get_proof(new_a);
            if (new_a.is_heq_proof())
                H = mk_to_eq_th(a_type, a, a_prime, H);
            expr Ba       = instantiate(abst_body(f_type), a);
            expr Ba_prime = instantiate(abst_body(f_type), a_prime);
            expr Bx       = abst_body(f_type);
            expr fa       = new_f(a);
            expr fx       = new_f(Var(0));
            expr result   = mk_subst_th(a_type, a, a_prime,
                                        mk_lambda(g_x, a_type, mk_heq(Ba, Bx, fa, fx)),
                                        mk_hrefl_th(Ba, fa),
                                        H);
            return some_expr(result);
        } else {
            expr const & new_A = abst_domain(new_f_type);
            expr a_type        = infer_type(a);
            expr new_a_type    = infer_type(new_a.m_expr);
            if (!is_convertible(new_a_type, new_A))
                return none_expr(); // failed
            expr Heq_a         = get_proof(new_a);
            bool is_heq_proof  = new_a.is_heq_proof();
            if (!is_definitionally_equal(A, a_type)|| !is_definitionally_equal(new_A, new_a_type)) {
                if (is_heq_proof) {
                    if (is_definitionally_equal(a_type, new_a_type) && is_definitionally_equal(A, new_A)) {
                        Heq_a        = mk_to_eq_th(a_type, a, new_a.m_expr, Heq_a);
                        is_heq_proof = false;
                    } else {
                        return none_expr(); // we don't know how to handle this case
                    }
                }
                Heq_a = translate_eq_proof(a_type, a, new_a.m_expr, Heq_a, A);
            }
            if (!is_heq_proof)
                Heq_a = mk_to_heq_th(A, a, new_a.m_expr, Heq_a);
            return some_expr(::lean::mk_hcongr_th(A,
                                                  new_A,
                                                  mk_lambda(f_type, abst_body(f_type)),
                                                  mk_lambda(new_f_type, abst_body(new_f_type)),
                                                  f, new_f, a, new_a.m_expr, Heq_f, Heq_a));
        }
    }

    /**
       \brief Given
                a            = b_res.m_expr  with proof b_res.m_proof
                b_res.m_expr = c             with proof H_bc
       This method returns a new result r s.t. r.m_expr == c and a proof of a = c
    */
    result mk_trans_result(expr const & a, result const & b_res, expr const & c, expr H_bc) {
        if (m_proofs_enabled) {
            if (!b_res.m_proof) {
                // The proof of a = b is reflexivity
                return result(c, H_bc);
            } else {
                expr const & b = b_res.m_expr;
                expr new_proof;
                bool heq_proof = false;
                if (b_res.is_heq_proof()) {
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
                a            = b_res.m_expr    with proof b_res.m_proof
                b_res.m_expr = c_res.m_expr    with proof c_res.m_proof

       This method returns a new result r s.t. r.m_expr == c and a proof of a = c_res.m_expr
    */
    result mk_trans_result(expr const & a, result const & b_res, result const & c_res) {
        if (m_proofs_enabled) {
            if (!b_res.m_proof) {
                // the proof of a == b is reflexivity
                return c_res;
            } else if (!c_res.m_proof) {
                // the proof of b == c is reflexivity
                return b_res.update_expr(c_res.m_expr);
            } else {
                bool heq_proof = b_res.is_heq_proof() || c_res.is_heq_proof();
                expr new_proof;
                expr const & b = b_res.m_expr;
                expr const & c = c_res.m_expr;
                if (heq_proof) {
                    expr a_type = infer_type(a);
                    expr b_type = infer_type(b);
                    expr c_type = infer_type(c);
                    expr H_ab   = *b_res.m_proof;
                    if (!b_res.is_heq_proof())
                        H_ab = mk_to_heq_th(a_type, a, b, H_ab);
                    expr H_bc   = *c_res.m_proof;
                    if (!c_res.is_heq_proof())
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
        if (m_has_cast && is_cast(e)) {
            // e is of the form (cast A B H a)
            //   a : A
            //   e : B
            expr A = arg(e, 1);
            expr B = arg(e, 2);
            expr H = arg(e, 3);
            expr a = arg(e, 4);
            if (m_proofs_enabled) {
                result res_a = simplify(a);
                expr c       = res_a.m_expr;
                if (res_a.m_proof) {
                    expr Hec;
                    expr Hac = *res_a.m_proof;
                    if (!res_a.is_heq_proof()) {
                        Hec = ::lean::mk_htrans_th(B, A, A, e, a, c,
                                                   update_app(e, 0, mk_cast_heq_fn()),  // cast A B H a == a
                                                   mk_to_heq_th(B, a, c, Hac));         // a == c
                    } else {
                        Hec = ::lean::mk_htrans_th(B, A, infer_type(c), e, a, c,
                                                   update_app(e, 0, mk_cast_heq_fn()),  // cast A B H a == a
                                                   Hac);                                // a == c
                    }
                    return result(c, Hec, true);

                } else {
                    // c is definitionally equal to a
                    // So, we use cast_heq theorem   cast_heq : cast A B H a == a
                    return result(c, update_app(e, 0, mk_cast_heq_fn()), true);
                }
            } else {
                return simplify(arg(e, 4));
            }
        }
        if (m_contextual) {
            expr const & f = arg(e, 0);
            for (auto congr_th : m_congr_thms) {
                if (congr_th->get_fun() == f)
                    return simplify_app_congr(e, *congr_th);
            }
        }
        return simplify_app_default(e);
    }

    /**
       \brief Make sure the proof in rhs is using homogeneous equality, and return true.
       If it is not possible to transform it in a homogeneous equality proof, then return false.
    */
    bool ensure_homogeneous(expr const & lhs, result & rhs) {
        if (rhs.is_heq_proof()) {
            // try to convert back to homogeneous
            lean_assert(rhs.m_proof);
            expr lhs_type = infer_type(lhs);
            expr rhs_type = infer_type(rhs.m_expr);
            if (is_definitionally_equal(lhs_type, rhs_type)) {
                // move back to homogeneous equality using to_eq
                rhs.m_proof = mk_to_eq_th(lhs_type, lhs, rhs.m_expr, *rhs.m_proof);
                return true;
            } else {
                return false;
            }
        } else {
            return true;
        }
    }

    void ensure_heterogeneous(expr const & lhs, result & rhs) {
        if (!rhs.is_heq_proof()) {
            rhs.m_proof     = mk_to_heq_th(infer_type(lhs), lhs, rhs.m_expr, get_proof(rhs));
            rhs.m_heq_proof = true;
        }
    }

    /**
       \brief Simplify \c e under the new assumption \c H.

       \remark \c H must be a constant of type P, where P is a proposition.

       \pre is_constant(H) && const_type(H)
    */
    result simplify_using(expr const & e, expr const & H) {
        lean_assert(is_constant(H) && const_type(H));
        updt_rule_set update(*this, H);
        return simplify(e);
    }

    /**
       \brief Simplify \c e using H : old_x == new_x
    */
    result simplify_remapping_constant(expr const & e, expr const & old_x, expr const & new_x, expr const & H) {
        updt_const_map update(*this, old_x, new_x, H);
        return simplify(e);
    }

    /**
       \brief Simplify \c e using the given congruence theorem.
       See congr.h for a description of congr_theorem_info.
    */
    result simplify_app_congr(expr const & e, congr_theorem_info const & cg_thm) {
        lean_assert(is_app(e));
        lean_assert(arg(e, 0) == cg_thm.get_fun());
        buffer<expr> new_args;
        bool changed = false;
        new_args.resize(num_args(e));
        new_args[0] = arg(e, 0);
        buffer<expr> proof_args_buf;
        expr *       proof_args = nullptr;
        if (m_proofs_enabled) {
            proof_args_buf.resize(cg_thm.get_num_proof_args() + 1);
            proof_args_buf[0] = cg_thm.get_proof();
            proof_args = proof_args_buf.data()+1;
        }
        for (auto const & info : cg_thm.get_arg_info()) {
            unsigned pos   = info.get_arg_pos();
            expr const & a = arg(e, pos);
            if (info.should_simplify()) {
                optional<congr_theorem_info::context> const & ctx = info.get_context();
                if (!ctx) {
                    // argument does not have a context
                    result res_a   = simplify(a);
                    new_args[pos] = res_a.m_expr;
                    if (m_proofs_enabled) {
                        if (!ensure_homogeneous(a, res_a))
                            return simplify_app_default(e); // fallback to default congruence
                        proof_args[info.get_pos_at_proof()]        = a;
                        proof_args[*info.get_new_pos_at_proof()]   = new_args[pos];
                        proof_args[*info.get_proof_pos_at_proof()] = get_proof(res_a);
                    }
                } else {
                    unsigned dep_pos = ctx->get_arg_pos();
                    expr C = ctx->use_new_val() ? new_args[dep_pos] : arg(e, dep_pos);
                    if (!ctx->is_pos_dep())
                        C = mk_not(C);
                    // We will simplify the \c a under the hypothesis C
                    expr H = mk_fresh_const(C);
                    result res_a  = simplify_using(a, H);
                    new_args[pos] = res_a.m_expr;
                    if (m_proofs_enabled) {
                        if (!ensure_homogeneous(a, res_a))
                            return simplify_app_default(e); // fallback to default congruence
                        proof_args[info.get_pos_at_proof()]        = a;
                        proof_args[*info.get_new_pos_at_proof()]   = new_args[pos];
                        name C_name(g_C, m_next_idx++); // H is a cryptic unique name
                        proof_args[*info.get_proof_pos_at_proof()] = mk_lambda(C_name, C, abstract(get_proof(res_a), H));
                    }
                }
                if (new_args[pos] != a)
                    changed = true;
            } else {
                // argument should not be simplified
                new_args[pos] = arg(e, pos);
                if (m_proofs_enabled)
                    proof_args[info.get_pos_at_proof()] = arg(e, pos);
            }
        }

        if (!changed) {
            return rewrite_app(e, result(e));
        } else if (!m_proofs_enabled) {
            return rewrite_app(e, result(mk_app(new_args)));
        } else {
            return rewrite_app(e, result(mk_app(new_args), mk_app(proof_args_buf)));
        }
    }

    result simplify_app_default(expr const & e) {
        lean_assert(is_app(e));
        buffer<expr>           new_args;
        buffer<optional<expr>> proofs;               // used only if m_proofs_enabled
        buffer<expr>           f_types, new_f_types; // used only if m_proofs_enabled
        buffer<bool>           heq_proofs;           // used only if m_has_heq && m_proofs_enabled
        bool changed = false;
        expr f       = arg(e, 0);
        expr f_type  = infer_type(f);
        result res_f = simplify(f);
        expr new_f   = res_f.m_expr;
        expr new_f_type;
        if (new_f != f)
            changed = true;
        new_args.push_back(new_f);
        if (m_proofs_enabled) {
            proofs.push_back(res_f.m_proof);
            f_types.push_back(f_type);
            new_f_type = res_f.is_heq_proof() ? infer_type(new_f) : f_type;
            new_f_types.push_back(new_f_type);
            if (m_has_heq)
                heq_proofs.push_back(res_f.is_heq_proof());
        }
        unsigned num = num_args(e);
        for (unsigned i = 1; i < num; i++) {
            f_type = ensure_pi(f_type);
            bool f_arrow   = is_arrow(f_type);
            expr const & a = arg(e, i);
            result res_a(a);
            if (m_has_heq || f_arrow) {
                res_a = simplify(a);
                if (res_a.m_expr != a)
                    changed = true;
            }
            expr new_a = res_a.m_expr;
            new_args.push_back(new_a);
            if (m_proofs_enabled) {
                proofs.push_back(res_a.m_proof);
                if (m_has_heq)
                    heq_proofs.push_back(res_a.is_heq_proof());
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
            } else if (m_has_heq && (heq_proofs[i] || !is_arrow(f_types[i-1]))) {
                expr f = mk_app_prefix(i, new_args);
                expr pr_i = *proofs[i];
                auto new_pr = mk_hcongr_th(f_types[i-1], f_types[i-1], f, f, mk_hrefl_th(f_types[i-1], f),
                                           arg(e, i), result(new_args[i], pr_i, heq_proofs[i]));
                if (!new_pr)
                    return rewrite_app(e, result(e)); // failed to create congruence proof
                pr = *new_pr;
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
                    expr pr_i = *proofs[i];
                    if (m_has_heq && heq_proofs[i]) {
                        if (!heq_proof)
                            pr = mk_to_heq_th(f_types[i], f, new_f, pr);
                        auto new_pr = mk_hcongr_th(f_types[i-1], new_f_types[i-1], f, new_f, pr,
                                                   arg(e, i), result(new_args[i], pr_i, true));
                        if (!new_pr)
                            return rewrite_app(e, result(e)); // failed to create congruence proof
                        pr = *new_pr;
                        heq_proof = true;
                    } else if (heq_proof) {
                        lean_assert(!heq_proofs[i]);
                        auto new_pr = mk_hcongr_th(f_types[i-1], new_f_types[i-1], f, new_f, pr,
                                                   arg(e, i), result(new_args[i], pr_i, false));
                        if (!new_pr)
                            return rewrite_app(e, result(e)); // failed to create congruence proof
                        pr = *new_pr;
                    } else {
                        pr = mk_congr_th(f_types[i-1], f, new_f, arg(e, i), new_args[i], pr, pr_i);
                    }
                } else if (heq_proof) {
                    auto new_pr = mk_hcongr_th(f_types[i-1], new_f_types[i-1], f, new_f, pr,
                                               arg(e, i), result(arg(e, i)));
                    if (!new_pr)
                        return rewrite_app(e, result(e)); // failed to create congruence proof
                    pr = *new_pr;
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
       \brief Given (applications) lhs and rhs s.t. lhs = rhs.m_expr
       with proof rhs.m_proof, this method applies rewrite rules, beta
       and evaluation to \c rhs.m_expr, and return a new result object
       new_rhs s.t.  lhs = new_rhs.m_expr with proof new_rhs.m_proof

       \pre is_app(lhs)
       \pre is_app(rhs.m_expr)
    */
    result rewrite_app(expr const & lhs, result const & rhs) {
        lean_assert(is_app(rhs.m_expr));
        lean_assert(is_app(lhs));
        if (evaluate_app(rhs.m_expr)) {
            // try to evaluate if all arguments are values.
            expr new_rhs = normalize(rhs.m_expr);
            if (is_value(new_rhs)) {
                // We don't need to create a new proof term since rhs.m_expr and new_rhs are
                // definitionally equal.
                return rewrite(lhs, rhs.update_expr(new_rhs));
            }
        }

        expr f   = arg(rhs.m_expr, 0);
        if (m_beta && is_lambda(f)) {
            expr new_rhs = head_beta_reduce(rhs.m_expr);
            // rhs.m_expr and new_rhs are also definitionally equal
            return rewrite(lhs, rhs.update_expr(new_rhs));
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
       \brief Given lhs and rhs s.t. lhs = rhs.m_expr with proof rhs.m_proof,
       this method applies rewrite rules, beta and evaluation to \c rhs.m_expr,
       and return a new result object new_rhs s.t.
                lhs = new_rhs.m_expr
       with proof new_rhs.m_proof
    */
    result rewrite(expr const & lhs, result const & rhs) {
        expr target = rhs.m_expr;
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
                                if (d_res.m_expr == True) {
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
                    result new_r2 = simplify(new_r1.m_expr);
                    return mk_trans_result(lhs, new_r1, new_r2);
                }
            }
        }
        if (!m_single_pass && lhs != rhs.m_expr) {
            result new_rhs = simplify(rhs.m_expr);
            return mk_trans_result(lhs, rhs, new_rhs);
        } else {
            return rhs;
        }
    }

    result simplify_constant(expr const & e) {
        lean_assert(is_constant(e));
        auto it = m_const_map.find(e);
        if (it != m_const_map.end()) {
            return it->second;
        } else if (m_unfold || m_eval) {
            auto obj = m_env->find_object(const_name(e));
            if (obj) {
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
       \brief Given (lambdas) lhs and rhs s.t. lhs = rhs.m_expr
       with proof rhs.m_proof, this method applies rewrite rules, and
       eta reduction, and return a new result object new_rhs s.t.
              lhs = new_rhs.m_expr with proof new_rhs.m_proof

       \pre is_lambda(lhs)
       \pre is_lambda(rhs.m_expr)
    */
    result rewrite_lambda(expr const & lhs, result const & rhs) {
        lean_assert(is_lambda(lhs));
        lean_assert(is_lambda(rhs.m_expr));
        if (m_eta && is_eta_target(rhs.m_expr)) {
            expr b = abst_body(rhs.m_expr);
            expr new_rhs;
            if (num_args(b) > 2) {
                new_rhs = mk_app(num_args(b) - 1, &arg(b, 0));
            } else {
                new_rhs = arg(b, 0);
            }
            new_rhs           = lower_free_vars(new_rhs, 1, 1);
            expr new_rhs_type = ensure_pi(infer_type(new_rhs));
            if (m_tc.is_definitionally_equal(abst_domain(new_rhs_type), abst_domain(rhs.m_expr), m_ctx)) {
                if (m_proofs_enabled) {
                    expr new_proof = mk_eta_th(abst_domain(rhs.m_expr),
                                               mk_lambda(rhs.m_expr, abst_body(new_rhs_type)),
                                               new_rhs);
                    return rewrite(lhs, mk_trans_result(lhs, rhs, new_rhs, new_proof));
                } else {
                    return rewrite(lhs, result(new_rhs));
                }
            }
        }
        return rewrite(lhs, rhs);
    }

    /**
       \brief Simplify only the body of the lambda expression, it does not 'touch' the domain.
    */
    result simplify_lambda_body(expr const & e) {
        lean_assert(is_lambda(e));
        expr const & d   = abst_domain(e);
        expr fresh_const = mk_fresh_const(d);
        expr bi          = instantiate(abst_body(e), fresh_const);
        result res_bi    = simplify(bi);
        expr new_bi    = res_bi.m_expr;
        if (is_eqp(new_bi, bi))
            return rewrite_lambda(e, result(e));
        expr new_e = mk_lambda(e, abstract(new_bi, fresh_const));
        if (!m_proofs_enabled || !res_bi.m_proof)
            return rewrite_lambda(e, result(new_e));
        if (res_bi.is_heq_proof()) {
            lean_assert(m_has_heq);
            // Using
            // theorem hsfunext {A : TypeM} {B B' : A → TypeU} {f : ∀ x, B x} {f' : ∀ x, B' x} :
            //     (∀ x, f x == f' x) → f == f'
            expr new_proof = mk_hsfunext_th(d,  // A
                                            mk_lambda(e, infer_type(abst_body(e))),                  // B
                                            mk_lambda(e, abstract(infer_type(new_bi), fresh_const)), // B'
                                            e,     // f
                                            new_e, // f'
                                            mk_lambda(g_x, d, abstract(*res_bi.m_proof, fresh_const)));
            return rewrite_lambda(e, result(new_e, new_proof, true));
        } else {
            expr body_type = infer_type(abst_body(e));
            // Using
            // axiom funext {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} (H : ∀ x : A, f x = g x) : f = g
            expr new_proof = mk_funext_th(d, mk_lambda(e, body_type), e, new_e,
                                          mk_lambda(e, abstract(*res_bi.m_proof, fresh_const)));
            return rewrite_lambda(e, result(new_e, new_proof));
        }
    }

    /**
       \brief Simplify a lambda abstraction when the heq module is available.
       In this case, we can simplify the domain and body of the lambda expression.
    */
    result simplify_lambda_with_heq(expr const & e) {
        expr const & d = abst_domain(e);
        result res_d   = simplify(d);
        expr new_d     = res_d.m_expr;
        if (is_eqp(d, new_d))
            return simplify_lambda_body(e);
        if (is_definitionally_equal(d, new_d))
            return simplify_lambda_body(update_lambda(e, new_d, abst_body(e)));
        // d and new_d are only provably equal, so we need to use hfunext
        expr x_old            = mk_fresh_const(d);
        expr x_new            = mk_fresh_const(new_d);
        expr x_old_eq_x_new   = mk_heq(d, new_d, x_old, x_new);
        expr H_x_old_eq_x_new = mk_fresh_const(x_old_eq_x_new);
        expr bi               = instantiate(abst_body(e), x_old);
        result res_bi         = simplify_remapping_constant(bi, x_old, x_new, H_x_old_eq_x_new);
        expr new_bi           = res_bi.m_expr;
        if (occurs(x_old, new_bi)) {
            // failed, simplifier didn't manage to replace x_old with x_new
            return rewrite(e, result(e));
        }
        expr new_e   = update_lambda(e, new_d, abstract(new_bi, x_new));
        if (!m_proofs_enabled)
            return rewrite(e, result(new_e));
        ensure_homogeneous(d, res_d);
        ensure_heterogeneous(bi, res_bi);
        // Using
        // axiom hfunext {A A' : TypeM} {B : A → TypeU} {B' : A' → TypeU} {f : ∀ x, B x} {f' : ∀ x, B' x} :
        //          A = A' → (∀ x x', x == x' → f x == f' x') → f == f'
        // Remark: the argument with type A = A' is actually @eq TypeM A A',
        // so we need to translate the proof d_eq_new_d_proof : d = new_d   to a TypeM equality proof
        expr d_eq_new_d_proof = translate_eq_typem_proof(d, res_d);
        expr new_proof = mk_hfunext_th(d,      // A
                                       new_d,  // A'
                                       Fun(x_old, d, infer_type(bi)),         // B
                                       Fun(x_new, new_d, infer_type(new_bi)), // B'
                                       e,      // f
                                       new_e,  // f'
                                       d_eq_new_d_proof, // A = A'
                                       // fun (x_old : d) (x_new : new_d) (H : x_old == x_new), bi == new_bi
                                       mk_lambda(abst_name(e), d,
                                                 mk_lambda(name(abst_name(e), 1), lift_free_vars(new_d, 0, 1),
                                                           mk_lambda(name(g_H, m_next_idx++), abstract(x_old_eq_x_new, {x_old, x_new}),
                                                                     abstract(*res_bi.m_proof, {x_old, x_new, H_x_old_eq_x_new})))));
        return rewrite(e, result(new_e, new_proof, true));
    }

    result simplify_lambda(expr const & e) {
        lean_assert(is_lambda(e));
        if (m_has_heq) {
            return simplify_lambda_with_heq(e);
        } else {
            return simplify_lambda_body(e);
        }
    }

    /**
       \brief Simplify A -> B when A -> B is a proposition.
    */
    result simplify_implication(expr const & e) {
        expr const & d = abst_domain(e);
        expr b = abst_body(e);
        if (m_contextual) {
            // Contextual simplification for A -> B
            // Rewrite A to A'
            // And rewrite B to B' using A'
            result res_d  = simplify(d);
            ensure_homogeneous(d, res_d);
            expr new_d    = res_d.m_expr;
            expr H        = mk_fresh_const(new_d);
            expr bi       = lower_free_vars(b, 1, 1);
            result res_bi = simplify_using(bi, H);
            expr new_bi   = res_bi.m_expr;
            ensure_homogeneous(bi, res_bi);
            if (is_eqp(new_d, d) && is_eqp(new_bi, bi))
                return rewrite(e, result(e));
            expr new_e = update_pi(e, new_d, lift_free_vars(new_bi, 0, 1));
            if (!m_proofs_enabled)
                return rewrite(e, result(new_e));
            name C_name(g_C, m_next_idx++);
            expr new_proof = mk_imp_congr_th(d, bi, new_d, new_bi,
                                             get_proof(res_d), mk_lambda(C_name, new_d, abstract(get_proof(res_bi), H)));
            return rewrite(e, result(new_e, new_proof));
        } else {
            // Simplify A -> B (when m_contextual == false)
            result res_d  = simplify(d);
            expr new_d    = res_d.m_expr;
            ensure_homogeneous(d, res_d);
            expr bi       = lower_free_vars(b, 1, 1);
            result res_bi = simplify(bi);
            expr new_bi   = res_bi.m_expr;
            ensure_homogeneous(bi, res_bi);
            if (is_eqp(new_d, d) && is_eqp(new_bi, bi))
                return rewrite(e, result(e));
            expr new_e = update_pi(e, new_d, lift_free_vars(new_bi, 0, 1));
            if (!m_proofs_enabled)
                return rewrite(e, result(new_e));
            expr new_proof = mk_imp_congr_th(d, bi, new_d, new_bi,
                                             get_proof(res_d), mk_lambda(g_H, new_d, lift_free_vars(get_proof(res_bi), 0, 1)));
            return rewrite(e, result(new_e, new_proof));
        }
    }

    /**
       \brief Simplify the domain of an arrow type A -> B when it is not a proposition.

       This procedure can be used even when the heq module is not available.
    */
    result simplify_arrow_domain(expr const & e) {
        lean_assert(is_arrow(e));
        expr const & A     = abst_domain(e);
        result res_A       = simplify(A);
        expr const & new_A = res_A.m_expr;
        if (is_eqp(A, new_A)) {
            return result(e);
        } else if (!m_proofs_enabled || is_definitionally_equal(A, new_A)) {
            return result(update_pi(e, new_A, abst_body(e)));
        } else {
            expr e_type        = infer_type(e);
            if (is_TypeU(e_type) || !ensure_homogeneous(A, res_A)) {
                return result(e); // failed, we can't use subst theorem
            } else {
                expr H = get_proof(res_A);
                // We create the following proof term for (@eq (e_type) (A -> B) (new_A -> B))
                //   @subst A_type A new_A (fun x : A_type, (@eq e_type (A -> B) (x -> B))) (@refl e_type (A -> B)) H
                expr A_type    = infer_type(A);
                expr x_arrow_B = update_pi(e, Var(0), abst_body(e));
                expr new_proof = mk_subst_th(A_type, A, new_A,
                                             mk_lambda(g_x, A_type, mk_eq(e_type, e, x_arrow_B)),
                                             mk_refl_th(e_type, e),
                                             H);
                return result(update_pi(e, new_A, abst_body(e)), new_proof);
            }
        }
    }

    /**
       \brief Simplify the body of an arrow type A -> B when it is not a proposition.

       This procedure can be used even when the heq module is not available.
    */
    result simplify_arrow_body(expr const & e) {
        lean_assert(is_arrow(e));
        expr const & B     = lower_free_vars(abst_body(e), 1, 1);
        result res_B       = simplify(B);
        expr const & new_B = res_B.m_expr;
        if (is_eqp(B, new_B)) {
            return result(e);
        } else if (!m_proofs_enabled || is_definitionally_equal(B, new_B)) {
            return result(update_pi(e, abst_domain(e), lift_free_vars(new_B, 1, 1)));
        } else {
            expr e_type        = infer_type(e);
            if (is_TypeU(e_type) || !ensure_homogeneous(B, res_B)) {
                return result(e); // failed, we can't use subst theorem
            } else {
                expr H = get_proof(res_B);
                // We create the following proof term for (@eq (e_type) (A -> B) (A -> new_B))
                //   @subst B_type B new_B (fun x : B_type, (@eq e_type (A -> B) (A -> x))) (@refl e_type (A -> B)) H
                expr B_type    = infer_type(B);
                expr A_arrow_x = update_pi(e, abst_domain(e), Var(1));
                expr new_proof = mk_subst_th(B_type, B, new_B,
                                             mk_lambda(g_x, B_type, mk_eq(e_type, e, A_arrow_x)),
                                             mk_refl_th(e_type, e),
                                             H);
                return result(update_pi(e, abst_domain(e), lift_free_vars(new_B, 1, 1)), new_proof);
            }
        }
    }

    /**
       \brief Simplify A -> B when A -> B is a not proposition.
    */
    result simplify_arrow(expr const & e) {
        result r1 = simplify_arrow_body(e);
        result r2 = simplify_arrow_domain(r1.m_expr);
        return rewrite(e, mk_trans_result(e, r1, r2));
    }

    /**
       \brief Simplify the body of (forall x : A, P x), when P x is a proposition.
    */
    result simplify_forall_body(expr const & e) {
        lean_assert(is_pi(e) && is_proposition(e));
        expr fresh_const = mk_fresh_const(abst_domain(e));
        expr const & d   = abst_domain(e);
        expr b           = abst_body(e);
        expr bi          = instantiate(b, fresh_const);
        result res_bi    = simplify(bi);
        expr new_bi      = res_bi.m_expr;
        if (is_eqp(new_bi, bi))
            return rewrite(e, result(e));
        expr new_e = mk_pi(abst_name(e), d, abstract(new_bi, fresh_const));
        if (!m_proofs_enabled || !res_bi.m_proof)
            return rewrite(e, result(new_e));
        ensure_homogeneous(bi, res_bi);
        expr new_proof = mk_allext_th(d,
                                      mk_lambda(e, b),
                                      mk_lambda(e, abst_body(new_e)),
                                      mk_lambda(e, abstract(*res_bi.m_proof, fresh_const)));
        return rewrite(e, result(new_e, new_proof));
    }

    /**
       \brief Simplify (forall x : A, P x) proposition when the heq module is available.
       In this case, we can simplify the domain and body of the forall expression.
    */
    result simplify_forall_with_heq(expr const & e) {
        lean_assert(is_pi(e) && is_proposition(e));
        // We don't support Pi's that are not proposition yet.
        // The problem is that
        //  axiom hpiext {A A' : TypeM} {B : A → TypeM} {B' : A' → TypeM} :
        //     A = A' → (∀ x x', x == x' → B x = B' x') → (∀ x, B x) = (∀ x, B' x)
        //  produces an equality in TypeM even if A, A', B and B' live in smaller universes.
        //
        // This limitation does not seem to be a big problem in practice.
        expr const & d = abst_domain(e);
        result res_d   = simplify(d);
        expr new_d     = res_d.m_expr;
        if (is_eqp(d, new_d))
            return simplify_forall_body(e);
        if (is_definitionally_equal(d, new_d))
            return simplify_forall_body(update_pi(e, new_d, abst_body(e)));
        // d and new_d are only provably equal, so we need to use hpiext or hallext
        expr x_old            = mk_fresh_const(d);
        expr x_new            = mk_fresh_const(new_d);
        expr x_old_eq_x_new   = mk_heq(d, new_d, x_old, x_new);
        expr H_x_old_eq_x_new = mk_fresh_const(x_old_eq_x_new);
        expr bi               = instantiate(abst_body(e), x_old);
        result res_bi         = simplify_remapping_constant(bi, x_old, x_new, H_x_old_eq_x_new);
        expr new_bi           = res_bi.m_expr;
        if (occurs(x_old, new_bi)) {
            // failed, simplifier didn't manage to replace x_old with x_new
            return rewrite(e, result(e));
        }
        expr new_e   = update_pi(e, new_d, abstract(new_bi, x_new));
        if (!m_proofs_enabled || is_definitionally_equal(e, new_e))
            return rewrite(e, result(new_e));
        ensure_homogeneous(d, res_d);
        ensure_homogeneous(bi, res_bi);
        // Remark: the argument with type A = A' in hallext and hpiext is actually @eq TypeM A A',
        // so we need to translate the proof d_eq_new_d_proof : d = new_d   to a TypeM equality proof
        expr d_eq_new_d_proof   = translate_eq_typem_proof(d, res_d);
        expr bi_eq_new_bi_proof = get_proof(res_bi);
        // Heqb : (∀ x x', x == x' → B x = B' x')
        expr Heqb = mk_lambda(abst_name(e), d,
                              mk_lambda(name(abst_name(e), 1), lift_free_vars(new_d, 0, 1),
                                        mk_lambda(name(g_H, m_next_idx++), abstract(x_old_eq_x_new, {x_old, x_new}),
                                                  abstract(bi_eq_new_bi_proof, {x_old, x_new, H_x_old_eq_x_new}))));
        // Using
        // theorem hallext {A A' : TypeM} {B : A → Bool} {B' : A' → Bool} :
        //    A = A' → (∀ x x', x == x' → B x = B' x') → (∀ x, B x) = (∀ x, B' x)
        expr new_proof = mk_hallext_th(d, new_d,
                                       Fun(x_old, d, bi),         // B
                                       Fun(x_new, new_d, new_bi), // B'
                                       d_eq_new_d_proof,          // A = A'
                                       Heqb);
        return rewrite(e, result(new_e, new_proof));
    }

    result simplify_pi(expr const & e) {
        lean_assert(is_pi(e));
        if (is_arrow(e)) {
            if (is_proposition(abst_domain(e)))
                return simplify_implication(e);
            else
                return simplify_arrow(e);
        } else if (is_proposition(e)) {
            if (m_has_heq)
                return simplify_forall_with_heq(e);
            else
                return simplify_forall_body(e);
        } else {
            // We currently do simplify (forall x : A, B x) when it is not a proposition.
            return result(e);
        }
    }

    result save(expr const & e, result const & r) {
        if (m_memoize) {
            result new_r = r.update_expr(m_max_sharing(r.m_expr));
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
        case expr_kind::Var:      return result(e);
        case expr_kind::Constant: return save(e, simplify_constant(e));
        case expr_kind::Type:
        case expr_kind::MetaVar:
        case expr_kind::Value:    return result(e);
        case expr_kind::App:      return save(e, simplify_app(e));
        case expr_kind::Lambda:   return save(e, simplify_lambda(e));
        case expr_kind::Pi:       return save(e, simplify_pi(e));
        case expr_kind::Let:      return save(e, simplify(instantiate(let_body(e), let_value(e))));
        }
        lean_unreachable();
    }

    void collect_congr_thms() {
        if (m_contextual) {
            for (auto const & rs : m_rule_sets) {
                rs.for_each_congr([&](congr_theorem_info const & info) {
                        if (std::all_of(m_congr_thms.begin(), m_congr_thms.end(),
                                        [&](congr_theorem_info const * info2) {
                                            return info2->get_fun() != info.get_fun(); })) {
                            m_congr_thms.push_back(&info);
                        }
                    });
            }
        }
    }

    void set_ctx(context const & ctx) {
        if (!is_eqp(m_ctx, ctx)) {
            m_cache.clear();
            m_ctx = ctx;
        }
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
        m_env(env), m_tc(env) {
        m_has_heq  = m_env->imported("heq");
        m_has_cast = m_env->imported("cast");
        set_options(o);
        if (m_contextual) {
            // We need an extra rule set if we are performing contextual rewriting
            m_rule_sets.push_back(rewrite_rule_set(env));
        }
        m_rule_sets.insert(m_rule_sets.end(), rs, rs + num_rs);
        collect_congr_thms();
        m_next_idx = 0;
    }

    expr_pair operator()(expr const & e, context const & ctx) {
        set_ctx(ctx);
        m_num_steps = 0;
        auto r = simplify(e);
        return mk_pair(r.m_expr, get_proof(r));
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
