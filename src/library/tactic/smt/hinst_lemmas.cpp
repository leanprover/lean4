/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "library/expr_lt.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/normalize.h"
#include "library/idx_metavar.h"
#include "library/type_context.h"
#include "library/annotation.h"
#include "library/exception.h"
#include "library/replace_visitor.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/smt/hinst_lemmas.h"

#ifndef LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS
#define LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS 1024
#endif

namespace lean {
/*
Step 1: Selecting which variables we should track.
Given (H : Pi (a_1 : A_1) ... (a_n : A_n), B) where B is not a Pi,
we use the following procedure to decide which a_i's must be in
patterns used by heuristic instantiation.
- We say an a_i that must occur in a pattern is "trackable".
- The set of "trackable" a_i's is the least fix point of
  a) If there is j > i, a_j is trackable, type(a_j) depends on a_i,
     and type(a_i) is not higher-order, then
     a_i is NOT trackable.
     Reason: we can infer a_i from a_j using type inference.
  b) a_i is a proposition -> a_i is NOT trackable.
     Reason: we leave a_i as hypothesis whenever we instantiate H.
  c) a_i is instance implicit -> a_i is NOT trackable.
     We should use type class resolution to infer a_i.

Remark: we say a (multi-)pattern for H is valid iff it contains all
trackable a_i's.
We define the set of "residue" hypotheses a_i as the least fix point of
  a) a_i is a proposition
  b) a_i is not inst_implicit
  c) a_i is not trackable
  d) a_i is not a proposition and there is no j > i s.t. a_j is not residue
     and type(a_j) depends on a_i, and type(a_i) is not higher-order

That is, if a_i is a "residue" hypothesis, we cannot infer it
by using type inference or type class resolution.
Residue hypotheses are the hypotheses for any instance of H produced by
the heuristic instantiation module.

Step 2a: H contains user-provided pattern hints
The user may provide pattern hints by annotating subterms of H using
the notation (:t:).
Example: The term (g x y) is a pattern hint at (H : forall x y, f (:g x y:) = x).

Let S be the set of patterns hints contained in H.
Then, a multi-pattern P is any subset of S s.t.
    a) P contains all trackable a_i's in H
    b) There is no strict subset of P that contains all trackable a_i's in H

If S is not empty, Lean will generate an error if there is no multi-pattern P for S.
The option pattern.max_steps is a threshold on the number of steps performed
Lean will generate an error if more than pattern.max_steps are performed while processing the set S.

Step 2b: H does NOT contain user-provided pattern hints.
When pattern hints are not provided, Lean uses a heuristic for selecting patterns.

- Lean will only consider terms that do NOT contain constants marked with the hint attribute
  [no_pattern]. In the standard library, we use this attribute to mark constants such as
  'and', 'or', 'not', 'iff', 'eq', 'heq', etc.

- Lean will look for candidate patterns in B and residue hypotheses.
Actually, it uses the following approach (TODO(Leo): should we provide options to control it?)
   1) Lean tries to find multi-patterns in B (only). If it finds at least one, then it is done, otherwise
   2) Lean tries to find multi-patterns in residue hypotheses only.
      If it finds at leat one, then it is done, otherwise
   3) Lean tries to find multi-patterns using residue hypotheses and B.
      If it can't find at least one, it signs an error.

- So, from now on, we will assume T is the set of terms where we will look for patterns.
We use trackable(p) to denote the set of trackable variables in p.
Lean will try to find "minimal" patterns and rank candidates in the following way
     Given terms p and q where both do not contain [no_pattern] constants, we say
     term p is "better" than q
     IFF
       1) trackable(p) is a strict superset of trackable(q) OR
       2) trackable(p) == trackable(q), but p is as subterm of q.

Given T, we collect a set of candidates C s.t., for each c_1 in C, there is no c_2 in C s.t. c_2 is better than c_1.
If there is c in C s.t. c contains all trackable a_i's, then all such c in C is our set of patterns (done).
To mimize the number of multi-patterns to be considered, we delete from C
any candidate c_1 in C if there is a c_2 in C s.t.
trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).

We say a subset M of C is a multi-pattern if M contains all trackable variables.

We say a multi-pattern M is minimal if no strict subset of M is a multi-pattern.
If the set of minimal multi-patterns for C is bigger than `pattern.max`, then we generate an error.
That is, the user should provide pattern-hints.
*/

static name * g_no_inst_pattern_attr = nullptr;

static basic_attribute const & get_no_inst_pattern_attribute() {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_no_inst_pattern_attr));
}

bool has_no_inst_pattern_attribute(environment const & env, name const & d) {
    return has_attribute(env, *g_no_inst_pattern_attr, d);
}

environment add_no_inst_pattern_attribute(environment const & env, name const & n) {
    return get_no_inst_pattern_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, true);
}

name_set get_no_inst_patterns(environment const & env) {
    buffer<name> ds;
    get_no_inst_pattern_attribute().get_instances(env, ds);
    return to_name_set(ds);
}

static name * g_pattern_hint = nullptr;

bool is_pattern_hint(expr const & e) { return is_annotation(e, *g_pattern_hint); }
expr const & get_pattern_hint_arg(expr const & e) { lean_assert(is_pattern_hint(e)); return get_annotation_arg(e); }
bool has_pattern_hints(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_pattern_hint(e); }));
}
expr mk_pattern_hint(expr const & e) {
    if (has_pattern_hints(e))
        throw exception("invalid pattern hint, nested patterns hints are not allowed");
    if (!is_app(e))
        throw generic_exception(e, "invalid pattern hint, pattern hints must be applications");
    return mk_annotation(*g_pattern_hint, e);
}

typedef rb_tree<unsigned, unsigned_cmp> idx_metavar_set;

static bool is_higher_order(type_context_old & ctx, expr const & e) {
    /* Remark: is it too expensive to use ctx.relaxed_whnf here? */
    return is_pi(ctx.whnf(ctx.infer(e)));
}

/** \brief Given type of the form (Pi (a_1 : A_1) ... (a_n : A_n), B) (or reducible to something of this form),
    create n idx_metavars (one for each a_i), store the meta-variables in mvars,
    and store in trackable and residue the subsets of these meta-variables as
    described in the beginning of this file. Then returns B (instantiated with the new meta-variables) */
expr extract_trackable(type_context_old & ctx, expr const & type,
                       buffer<expr> & mvars,
                       buffer<bool> & inst_implicit_flags,
                       idx_metavar_set & trackable, idx_metavar_set & residue) {
    // 1. Create mvars and initialize trackable and residue sets
    expr it = type;
    while (true) {
        if (!is_pi(it)) {
            expr new_it = ctx.relaxed_whnf(it);
            if (!is_pi(new_it))
                break; // consumed all arguments
            it = new_it;
        }
        lean_assert(is_pi(it));
        expr new_mvar = ctx.mk_tmp_mvar(binding_domain(it));
        lean_assert(is_idx_metavar(new_mvar));
        mvars.push_back(new_mvar);
        bool is_inst_implicit = binding_info(it).is_inst_implicit();
        inst_implicit_flags.push_back(is_inst_implicit);
        bool is_prop          = ctx.is_prop(binding_domain(it));
        if (!is_inst_implicit) {
            unsigned midx = to_meta_idx(new_mvar);
            if (is_prop)
                residue.insert(midx);
            else
                trackable.insert(midx);
        }
        it = instantiate(binding_body(it), new_mvar);
    }
    expr     B = it;
    unsigned n = mvars.size();
    // 2. Compute trackable fixpoint
    bool modified;
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!trackable.contains(midx))
                continue; // variable is not in the trackable set
            // There is no j > i, mvars[j] is trackable, type(mvars[j]) depends on mvars[i],
            // and type(mvars[i]) is not higher-order.
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (trackable.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            trackable.erase(midx);
            modified = true;
        }
    } while (modified);
    // 3. Compute residue fixpoint
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!residue.contains(midx))
                continue; // variable is not in the residue set
            // There is no j > i s.t. mvars[j] is not residue
            // and type(mvars[j]) depends on mvars[i], and type(mvars[i]) is not higher-order
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (!residue.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            residue.erase(midx);
            modified = true;
        }
    } while (modified);
    return B;
}

static expr dsimp(type_context_old & ctx, transparency_mode md, expr const & e) {
    /* We used to use ::lean::normalize here, but it was bad since it would unfold type class instances.
       First, this may be a performance problem.
       Second, it would expose a problem with the way we define some algebraic structures.
       See discussion at ring.lean.
    */
    defeq_can_state dcs;
    dsimp_config cfg;
    cfg.m_md                 = md;
    cfg.m_canonize_instances = false;
    cfg.m_max_steps          = 1000000; /* TODO(Leo): add parameter? */
    cfg.m_eta                = true;
    return dsimplify_fn(ctx, dcs, simp_lemmas_for(), list<name>(), cfg)(e);
}

struct mk_hinst_lemma_fn {
    type_context_old &     m_ctx;
    transparency_mode  m_md_norm;
    name_set           m_no_inst_patterns;
    expr               m_H;
    unsigned           m_num_uvars;
    unsigned           m_max_steps;
    /* If m_simp is true, the pattern inference procedure assumes the given lemma is a [simp] lemma.
       That is, the conclusion is of the form (t ~ s), and it will try to use t as a pattern. */
    bool               m_simp;

    buffer<expr>       m_mvars;
    idx_metavar_set    m_trackable;
    idx_metavar_set    m_residue;
    unsigned           m_num_steps;
    name               m_id;

    mk_hinst_lemma_fn(type_context_old & ctx, transparency_mode md_norm, expr const & H,
                      unsigned num_uvars, unsigned max_steps, bool simp,
                      name const & id):
        m_ctx(ctx), m_md_norm(md_norm),
        m_no_inst_patterns(get_no_inst_patterns(ctx.env())),
        m_H(H), m_num_uvars(num_uvars), m_max_steps(max_steps),
        m_simp(simp), m_id(id) {}

    struct candidate {
        expr            m_expr;
        idx_metavar_set m_mvars;
        candidate() {}
        candidate(expr const & e):
            m_expr(e) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (is_idx_metavar(e))
                        m_mvars.insert(to_meta_idx(e));
                    return true;
                });
        }
        candidate(expr const & e, idx_metavar_set const & mvars):m_expr(e), m_mvars(mvars) {}
    };

    struct candidate_lt {
        int operator()(candidate const & c1, candidate const & c2) const { return expr_quick_cmp()(c1.m_expr, c2.m_expr); }
    };

    typedef rb_tree<candidate, candidate_lt> candidate_set;

    expr normalize(expr const & e) {
        return dsimp(m_ctx, m_md_norm, e);
    }

    void collect_pattern_hints(expr const & e, candidate_set & s) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_pattern_hint(e)) {
                    expr hint = get_pattern_hint_arg(e);
                    // TODO(Leo): if hint was unfolded and is not an application anymore, we should
                    // report to user this fact.
                    if (is_app(hint)) {
                        s.insert(candidate(normalize(hint)));
                    }
                    return false;
                }
                return true;
            });
    }

    candidate_set collect_pattern_hints(buffer<expr> const & mvars, buffer<expr> const & residue, expr const & B) {
        candidate_set s;
        for (expr const & mvar : mvars)
            collect_pattern_hints(m_ctx.infer(mvar), s);
        for (expr const & r : residue)
            collect_pattern_hints(m_ctx.infer(r), s);
        collect_pattern_hints(B, s);
        return s;
    }

    candidate_set m_candidates;

    void save_candidates(candidate_set const & s) {
        m_candidates.merge(s);
    }

    candidate_set collect_core(expr const & a) {
        switch (a.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:   case expr_kind::Constant:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Pi:
            return candidate_set();
        case expr_kind::Let:
            /* TODO(Leo): Decide whether we should support let-expressions or not.
               IF we don't, then we should report this occurrence users. */
            return candidate_set();
        case expr_kind::Lambda:
            if (has_idx_metavar(a))
                return candidate_set(candidate(a));
            else
                return candidate_set();
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                candidate_set s = collect_core(macro_arg(a, i));
                save_candidates(s);
            }
            return candidate_set();
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(a, args);
            buffer<candidate_set> arg_candidates;
            bool forbidden = !is_local(fn) && (!is_constant(fn) || m_no_inst_patterns.contains(const_name(fn)));
            if (forbidden) {
                for (expr const & arg : args) {
                    candidate_set s = collect_core(arg);
                    save_candidates(s);
                }
                return candidate_set();
            } else {
                candidate_set ss;
                idx_metavar_set mvars;
                for (expr const & arg : args) {
                    if (is_idx_metavar(arg)) {
                        if (m_trackable.contains(to_meta_idx(arg))) {
                            mvars.insert(to_meta_idx(arg));
                        }
                    } else {
                        candidate_set s = collect_core(arg);
                        s.for_each([&](candidate const & c) {
                                ss.insert(c);
                                mvars.merge(c.m_mvars);
                            });
                    }
                }
                if (ss.find_if([&](candidate const & c) { return mvars == c.m_mvars; })) {
                    return ss;
                } else if (!mvars.empty()) {
                    // a subsumes all children candidates
                    return candidate_set(candidate(a, mvars));
                } else {
                    return candidate_set();
                }
            }
        }}
        lean_unreachable();
    }

    candidate_set collect(expr const & a) {
        m_candidates = candidate_set();
        if (m_simp) {
            expr lhs, rhs;
            if (is_eq(a, lhs, rhs) || is_heq(a, lhs, rhs) || is_iff(a, lhs, rhs)) {
                m_candidates.insert(candidate(normalize(lhs)));
            }
        } else {
            save_candidates(collect_core(normalize(a)));
        }
        return m_candidates;
    }

    void mk_multi_patterns_core(unsigned i, buffer<candidate> const & s, buffer<expr> & mp, idx_metavar_set const & mvars, buffer<multi_pattern> & mps) {
        m_num_steps++;
        if (m_num_steps > m_max_steps)
            throw exception(sstream() << "pattern inference failed for '" << m_id << "', the maximum number (" << m_max_steps << ") of steps has been reached "
                            "(possible solutions: provide pattern hints using the notation '(: t :)' for marking subterms; increase threshold using option pattern.max_steps)");
        if (i == s.size())
            return;
        candidate const & c = s[i];
        if (!mvars.is_strict_superset(c.m_mvars)) {
            // candidate s[i] contributes with new variables
            unsigned sz = mp.size();
            mp.push_back(c.m_expr);
            idx_metavar_set new_mvars = mvars;
            new_mvars.merge(c.m_mvars);
            if (new_mvars.is_superset(m_trackable)) {
                // found multi-pattern
                mps.push_back(to_list(mp));
            } else {
                // include s[i]
                mk_multi_patterns_core(i+1, s, mp, new_mvars, mps);
            }
            mp.shrink(sz);
        }
        // do not include s[i];
        mk_multi_patterns_core(i+1, s, mp, mvars, mps);
    }

    /* If heuristic is true, then
       1. Give preference to unary patterns
       2. If there are no unary patterns, then
          a) delete any candidate c_1 if there is a c_2 s.t.
             trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).
          b) delete any candidate c_1 if there is a c_2 s.t.
             c_1 is a subterm of c_2, and c_2.m_vars is a strict superset of c_1.m_vars */
    list<multi_pattern> mk_multi_patterns_using(candidate_set s, bool heuristic) {
        if (heuristic) {
            buffer<multi_pattern> unit_patterns;
            s.for_each([&](candidate const & c) {
                    if (c.m_mvars.is_superset(m_trackable))
                        unit_patterns.push_back(to_list(c.m_expr));
                });
            if (!unit_patterns.empty()) {
                return to_list(unit_patterns);
            }
            buffer<candidate> to_delete;
            s.for_each([&](candidate const & c_1) {
                    if (s.find_if([&](candidate const & c_2) {
                                return
                                    //      a) delete any candidate c_1 if there is a c_2 s.t.
                                    //         trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).
                                    (c_1.m_mvars == c_2.m_mvars && get_weight(c_1.m_expr) > get_weight(c_2.m_expr)) ||
                                    //      b) delete any candidate c_1 if there is a c_2 s.t.
                                    //         c_1 is a subterm of c_2, and c_2.m_vars is a strict superset of c_1.m_vars
                                    (occurs(c_1.m_expr, c_2.m_expr) && c_2.m_mvars.is_strict_superset(c_1.m_mvars));
                            })) {
                        to_delete.push_back(c_1);
                    }
                });
            for (candidate const & c : to_delete) {
                s.erase(c);
            }
        }
        buffer<candidate> s_buffer;
        s.to_buffer(s_buffer);
        buffer<multi_pattern> mps;
        buffer<expr> mp;
        m_num_steps = 0;
        mk_multi_patterns_core(0, s_buffer, mp, idx_metavar_set(), mps);
        return to_list(mps);
    }

    expr replace_mvars(expr const & e, buffer<expr> const & subst) {
        return replace(e,
                       [&](expr const & e) {
                           if (!has_expr_metavar(e))
                               return some_expr(e);
                           if (is_idx_metavar(e))
                               return some_expr(subst[to_meta_idx(e)]);
                           else
                               return none_expr();
                       });
    }

    /* Create proof by pushing all residue hypotheses to the "end".
       Residue hypotheses are converted into local constants.
       Remaining metavariables are "renamed" (i.e., renumbered to avoid gaps due to residue hypotheses moved to the end).
       Trackable set is updated.
       subst will contain the mvars renaming */
    expr mk_proof(type_context_old::tmp_locals & locals, buffer<expr> & new_residue, buffer<expr> & subst) {
        unsigned j = 0;
        bool found_residue     = false;
        bool only_tail_residue = true;
        for (unsigned i = 0; i < m_mvars.size(); i++) {
            expr new_type = m_ctx.infer(m_mvars[i]);
            if (i != j)
                new_type = replace_mvars(new_type, subst);
            if (m_residue.contains(to_meta_idx(m_mvars[i]))) {
                found_residue = true;
                expr res      = locals.push_local("_x", new_type);
                new_residue.push_back(res);
                subst.push_back(res);
            } else {
                if (found_residue)
                    only_tail_residue = false;
                expr new_mvar;
                if (j == i) {
                    new_mvar = m_mvars[i];
                } else {
                    new_mvar = mk_idx_metavar(j, new_type);
                    if (m_trackable.contains(i)) {
                        m_trackable.erase(i);
                        m_trackable.insert(j);
                    }
                    m_mvars[j] = new_mvar;
                }
                j++;
                subst.push_back(new_mvar);
            }
        }
        m_mvars.shrink(j);
        if (only_tail_residue) {
            return mk_app(m_H, m_mvars);
        } else {
            return locals.mk_lambda(mk_app(m_H, subst));
        }
    }

    struct try_again_without_hints {};

    struct erase_hints_fn : public replace_visitor {
        virtual expr visit_macro(expr const & e) override {
            if (is_pattern_hint(e)) {
                return visit(get_annotation_arg(e));
            } else {
                return replace_visitor::visit_macro(e);
            }
        }
    };

    hinst_lemma operator()(bool erase_hints) {
        expr H_type = m_ctx.infer(m_H);
        if (erase_hints) {
            H_type = erase_hints_fn()(H_type);
        }
        buffer<bool> inst_implicit_flags;
        expr B      = extract_trackable(m_ctx, H_type, m_mvars, inst_implicit_flags, m_trackable, m_residue);
        lean_assert(m_mvars.size() == inst_implicit_flags.size());
        buffer<expr> subst;
        buffer<expr> residue_locals;
        type_context_old::tmp_locals locals(m_ctx);
        expr proof  = mk_proof(locals, residue_locals, subst);
        B           = replace_mvars(B, subst);
        candidate_set hints = collect_pattern_hints(m_mvars, residue_locals, B);
        list<multi_pattern> mps;
        if (!hints.empty()) {
            mps = mk_multi_patterns_using(hints, false);
        } else {
            if (has_pattern_hints(H_type)) {
                throw try_again_without_hints();
            }
            buffer<expr> places;
            candidate_set B_candidates = collect(B);
            if (auto r1 = mk_multi_patterns_using(B_candidates, true)) {
                mps = r1;
            } else if (!m_simp) {
                candidate_set residue_candidates;
                for (expr const & r : residue_locals) {
                    residue_candidates.merge(collect(m_ctx.infer(r)));
                }
                if (auto r2 = mk_multi_patterns_using(residue_candidates, true)) {
                    mps = r2;
                } else if (!residue_candidates.empty() && !B_candidates.empty()) {
                    candidate_set all_candidates = B_candidates;
                    all_candidates.merge(residue_candidates);
                    mps = mk_multi_patterns_using(all_candidates, true);
                }
            }
        }
        if (!mps) {
            throw exception(sstream() << "pattern inference failed for '" << m_id << "', "
                            "(solution: provide pattern hints using the notation '(: t :)' )");
        }
        hinst_lemma r;
        r.m_id               = m_id;
        r.m_num_uvars        = m_num_uvars;
        r.m_num_mvars        = m_mvars.size();
        r.m_multi_patterns   = mps;
        r.m_mvars            = to_list(m_mvars);
        r.m_is_inst_implicit = to_list(inst_implicit_flags);
        r.m_prop             = m_ctx.infer(proof);
        r.m_proof            = proof;
        r.m_expr             = m_H;
        return r;
    }
};

hinst_lemma mk_hinst_lemma_core(type_context_old & ctx, transparency_mode md_norm, expr const & H, unsigned num_uvars,
                                unsigned max_steps, bool simp, name const & id) {
    if (num_uvars == 0 && !is_pi(ctx.relaxed_whnf(ctx.infer(H)))) {
        hinst_lemma h;
        h.m_id    = id;
        h.m_proof = H;
        h.m_prop  = dsimp(ctx, md_norm, ctx.infer(h.m_proof));
        h.m_expr  = h.m_proof;
        return h;
    } else {
        try {
            type_context_old::tmp_mode_scope tscope(ctx, num_uvars, 0);
            bool erase_hints = false;
            return mk_hinst_lemma_fn(ctx, md_norm, H, num_uvars, max_steps, simp, id)(erase_hints);
        } catch (mk_hinst_lemma_fn::try_again_without_hints &) {
            type_context_old::tmp_mode_scope tscope(ctx, num_uvars, 0);
            try {
                bool erase_hints = true;
                return mk_hinst_lemma_fn(ctx, md_norm, H, num_uvars, max_steps, simp, id)(erase_hints);
            } catch (mk_hinst_lemma_fn::try_again_without_hints &) {
                lean_unreachable();
            }
        }
    }
}

static name * g_hinst_lemma_max_steps = nullptr;

unsigned get_hinst_lemma_max_steps(options const & o) {
    return o.get_unsigned(*g_hinst_lemma_max_steps, LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS);
}

hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, expr const & H, bool simp) {
    unsigned max_steps = get_hinst_lemma_max_steps(ctx.get_options());
    name id;
    if (is_local(H))
        id = mlocal_pp_name(H);
    return mk_hinst_lemma_core(ctx, md_norm, H, 0, max_steps, simp, id);
}

hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, name const & c, bool simp) {
    unsigned max_steps = get_hinst_lemma_max_steps(ctx.get_options());
    declaration const & d = ctx.env().get(c);
    buffer<level> us;
    unsigned num_us = d.get_num_univ_params();
    for (unsigned i = 0; i < num_us; i++)
        us.push_back(mk_idx_metauniv(i));
    expr H          = mk_constant(c, to_list(us));
    name id         = c;
    return mk_hinst_lemma_core(ctx, md_norm, H, num_us, max_steps, simp, id);
}

format pp_hinst_lemma(formatter const & fmt, hinst_lemma const & h) {
    format r;
    r += format(h.m_id) + comma() + line();
    bool first1 = true;
    format pats;
    for (multi_pattern const & mp : h.m_multi_patterns) {
        if (first1) first1 = false; else pats += comma() + line();
        format pat;
        bool first2 = true;
        for (expr const & p : mp) {
            if (first2) first2 = false; else pat += comma() + line();
            pat += fmt(p);
        }
        pats += group(bracket("{", pat, "}"));
    }
    char const * n = "patterns:";
    r += nest(strlen(n), format(n) + line() + group(bracket("{", pats, "}")));
    return group(bracket("[", r, "]"));
}

struct vm_hinst_lemma : public vm_external {
    hinst_lemma m_val;
    vm_hinst_lemma(hinst_lemma const & v): m_val(v) {}
    virtual ~vm_hinst_lemma() {}
    virtual void dealloc() override { this->~vm_hinst_lemma(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemma), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_hinst_lemma(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_hinst_lemma))) vm_hinst_lemma(m_val); }
};

hinst_lemma const & to_hinst_lemma(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_hinst_lemma*>(to_external(o)));
    return static_cast<vm_hinst_lemma*>(to_external(o))->m_val;
}

vm_obj to_obj(hinst_lemma const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemma))) vm_hinst_lemma(s));
}

vm_obj hinst_lemma_mk_core(vm_obj const & m, vm_obj const & lemma, vm_obj const & simp, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context_old ctx        = mk_type_context_for(s);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_transparency_mode(m), to_expr(lemma), to_bool(simp));
    return tactic::mk_success(to_obj(h), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj hinst_lemma_mk_from_decl_core(vm_obj const & m, vm_obj const & lemma_name, vm_obj const & simp, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context_old ctx        = mk_type_context_for(s);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_transparency_mode(m), to_name(lemma_name), to_bool(simp));
    return tactic::mk_success(to_obj(h), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj hinst_lemma_pp(vm_obj const & h, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    type_context_old ctx = mk_type_context_for(s);
    formatter fmt = fmtf(s.env(), s.get_options(), ctx);
    format r = pp_hinst_lemma(fmt, to_hinst_lemma(h));
    return tactic::mk_success(to_obj(r), s);
    LEAN_TACTIC_CATCH(s);
}

struct vm_hinst_lemmas : public vm_external {
    hinst_lemmas m_val;
    vm_hinst_lemmas(hinst_lemmas const & v): m_val(v) {}
    virtual ~vm_hinst_lemmas() {}
    virtual void dealloc() override { this->~vm_hinst_lemmas(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemmas), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_hinst_lemmas(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_hinst_lemmas))) vm_hinst_lemmas(m_val); }
};

hinst_lemmas const & to_hinst_lemmas(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_hinst_lemmas*>(to_external(o)));
    return static_cast<vm_hinst_lemmas*>(to_external(o))->m_val;
}

bool is_hinst_lemmas(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_hinst_lemmas*>(to_external(o));
}

vm_obj to_obj(hinst_lemmas const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemmas))) vm_hinst_lemmas(s));
}

vm_obj hinst_lemmas_mk() {
    return to_obj(hinst_lemmas());
}

vm_obj hinst_lemmas_add(vm_obj const & hls, vm_obj const & h) {
    hinst_lemmas new_lemmas = to_hinst_lemmas(hls);
    new_lemmas.insert(to_hinst_lemma(h));
    return to_obj(new_lemmas);
}

vm_obj hinst_lemmas_fold(vm_obj const &, vm_obj const & hls, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    to_hinst_lemmas(hls).for_each([&](hinst_lemma const & h) {
            r = invoke(fn, to_obj(h), r);
        });
    return r;
}

vm_obj hinst_lemmas_merge(vm_obj const & s1, vm_obj const & s2) {
    hinst_lemmas r = to_hinst_lemmas(s1);
    r.merge(to_hinst_lemmas(s2));
    return to_obj(r);
}

void initialize_hinst_lemmas() {
    g_pattern_hint      = new name("pattern_hint");
    register_annotation(*g_pattern_hint);
    g_no_inst_pattern_attr = new name({"no_inst_pattern"});
    /* Add validation */
    register_system_attribute(basic_attribute(*g_no_inst_pattern_attr, "do not consider terms containing this declaration in the pattern inference procedure"));

    g_hinst_lemma_max_steps = new name{"hinst_lemma", "pattern", "max_steps"};

    register_unsigned_option(*g_hinst_lemma_max_steps, LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS,
                             "(hinst_lemma) max number of steps performed by pattern inference procedure for heuristic instantiation lemmas, "
                             "we have this threshold because in the worst case this procedure may take "
                             "an exponetial number of steps");

    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_core"}),           hinst_lemma_mk_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_from_decl_core"}), hinst_lemma_mk_from_decl_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "pp"}),                hinst_lemma_pp);

    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "mk"}),               hinst_lemmas_mk);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "add"}),              hinst_lemmas_add);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "fold"}),             hinst_lemmas_fold);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "merge"}),            hinst_lemmas_merge);
}

void finalize_hinst_lemmas() {
    delete g_pattern_hint;
    delete g_no_inst_pattern_attr;
    delete g_hinst_lemma_max_steps;
}
}
