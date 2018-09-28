/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <memory>
#include <utility>
#include <algorithm>
#include "util/lbool.h"
#include "util/name_set.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/local_ctx.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"

namespace lean {
/** \brief Type checker used by the compiler. It relaxes the type checking rules, and supports
    extensions that useful to justify some of the compiler transformations we use.

    - The constant `lc_any : Type` is considered to be definitionally equal to any term `t : Sort u`.

    - All propositions `p q : Prop` are considered definitionally equal.

    - All proofs `h_1 : p : Prop` and `h_2 : q : Prop` are considered definitionally equal.
      Thus, we can use `def lc_proof : true := true.mk` to erase proofs.

    - The constant `lc_unreachable : lc_any` is used to represent unreachable code.

    - We use the constant `lc_cast A B t` to represent type casts from `A` to `B` for `t : A`.

    - Universes levels are not checked, but we propagate them when inferring types.

    - Support for `I._cases` terms. They are encoded as
      applications of auxiliary `I._cases` constants, where the number
      of arguments is 2 + number of constructors of `I`.  The first
      argument is the resulting type, the second is the major premise,
      and the remaining are the minor premises. This type checker has
      support for reducing and type checking this kind of application.

    - We say a term `t` is stuck IF
       1) `t` is a free variable or axiom (i.e., constant_info is axiom_info).
       2) `t` is an application `f a`, and `f` is stuck.
       3) `t` is an projection `p.i`, and `p` is stuck.
       4) `t` is a recursor application `I.rec ... m ...` where `m` is the major premise,
          and `m` is stuck. We also consider partially applied
          `I.rec ...` applications to be stuck.
       5) Similar to item 3, but with `I._cases` instead of `I.rec`.

    - We say a type `t` is type_stuck if it is stuck and it is an application or projection.

    - Given types `t` and `s`, we consider them to be definitionally equal if `t` or `s` is type_stuck, or
      `t` or `s` is `lc_any`.

    - We propagate `lc_any` when inferring types. Examples:
      * When inferring the type of `f a`, if the type of `f` is stuck or is `lc_any`, the result is `lc_any`.
      * When inferring the type of `p.i`, if the type of `p` is stuck or is `lc_any`, the result is `lc_any`.

    - Support for trivial structures.
      We say a structure `I As` is trivial if it has only constructor,
      the constructor has only one relevant field, and the type of this field is `C As` and
      doesn't depend on other fields. Moreover, we consider the types `I As` and `C As` to be
      definitionally equal, and the constructor to be the identity function.

    - `quot A r` and `A` are considered definitionally equal.

    - `quot.mk` is treated as the identity function.

    - `@quot.lift α r β f h a` reduces to `f a`. */
class ctype_checker {
public:
    class state {
        typedef expr_map<expr> infer_cache;
        typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> expr_pair_set;
        environment               m_env;
        name_generator            m_ngen;
        infer_cache               m_infer_type[2];
        friend ctype_checker;
    public:
        state(environment const & env);
        environment & env() { return m_env; }
        environment const & env() const { return m_env; }
        name_generator & ngen() { return m_ngen; }
    };
private:
    bool                      m_st_owner;
    state *                   m_st;
    local_ctx                 m_lctx;

    expr ensure_sort_core(expr e, expr const & s);
    expr ensure_pi_core(expr e, expr const & s);
    expr infer_fvar(expr const & e);
    expr infer_constant(expr const & e);
    expr infer_lambda(expr const & e, bool infer_only);
    expr infer_pi(expr const & e, bool infer_only);
    expr infer_app(expr const & e, bool infer_only);
    expr infer_proj(expr const & e, bool infer_only);
    expr infer_let(expr const & e, bool infer_only);
    expr infer_type_core(expr const & e, bool infer_only);
    expr infer_type(expr const & e);

    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };
    optional<expr> reduce_recursor(expr const & e);
    optional<expr> reduce_proj(expr const & e);
    expr whnf_fvar(expr const & e);
    expr whnf_core(expr const & e);
    optional<constant_info> is_delta(expr const & e) const;
    optional<expr> unfold_definition_core(expr const & e);
    optional<expr> unfold_definition(expr const & e);

    bool is_def_eq_binding(expr t, expr s);
    lbool quick_is_def_eq(expr const & t, expr const & s);
    bool is_def_eq_args(expr t, expr s);
    bool try_eta_expansion_core(expr const & t, expr const & s);
    bool try_eta_expansion(expr const & t, expr const & s) {
        return try_eta_expansion_core(t, s) || try_eta_expansion_core(s, t);
    }
    bool is_def_eq_app(expr const & t, expr const & s);
    bool is_def_eq_proof_irrel(expr const & t, expr const & s);
    reduction_status lazy_delta_reduction_step(expr & t_n, expr & s_n);
    lbool lazy_delta_reduction(expr & t_n, expr & s_n);
    bool is_def_eq_core(expr const & t, expr const & s);
    /** \brief Like \c check, but ignores undefined universes */
    expr check_ignore_undefined_universes(expr const & e);

public:
    ctype_checker(state & st, local_ctx const & lctx);
    ctype_checker(state & st):ctype_checker(st, local_ctx()) {}
    ctype_checker(environment const & env, local_ctx const & lctx);
    ctype_checker(environment const & env):ctype_checker(env, local_ctx()) {}
    ctype_checker(ctype_checker &&);
    ctype_checker(ctype_checker const &) = delete;
    ~ctype_checker();

    environment const & env() const { return m_st->m_env; }

    /** \brief Return the type of \c t.
        It does not check whether the input expression is type correct or not.
        The contract is: IF the input expression is type correct, then the inferred
        type is correct.
        Throw an exception if a type error is found. */
    expr infer(expr const & t) { return infer_type(t); }

    /** \brief Type check the given expression, and return the type of \c t.
        Throw an exception if a type error is found. */
    expr check(expr const & t);

    /** \brief Return true iff t is definitionally equal to s. */
    bool is_def_eq(expr const & t, expr const & s);
    /** \brief Return true iff t is a proposition. */
    bool is_prop(expr const & t);
    /** \brief Return the weak head normal form of \c t. */
    expr whnf(expr const & t);
    /** \brief Return a Pi if \c t is convertible to a Pi type. Throw an exception otherwise.
        The argument \c s is used when reporting errors */
    expr ensure_pi(expr const & t, expr const & s);
    expr ensure_pi(expr const & t) { return ensure_pi(t, t); }
    /** \brief Mare sure type of \c e is a Pi, and return it. Throw an exception otherwise. */
    expr ensure_fun(expr const & e) { return ensure_pi(infer(e), e); }
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise.
        The argument \c s is used when reporting errors. */
    expr ensure_sort(expr const & t, expr const & s);
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise. */
    expr ensure_sort(expr const & t) { return ensure_sort(t, t); }
    /** \brief Mare sure type of \c e is a sort, and return it. Throw an exception otherwise. */
    expr ensure_type(expr const & e) { return ensure_sort(infer(e), e); }
    expr eta_expand(expr const & e);
};

void initialize_ctype_checker();
void finalize_ctype_checker();
}
