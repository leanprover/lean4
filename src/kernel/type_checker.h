/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <memory>
#include <utility>
#include <algorithm>
#include "util/lbool.h"
#include "util/flet.h"
#include "util/name_set.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/expr_pair.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "kernel/abstract_type_context.h"

namespace lean {
/** \brief Lean Type Checker. It can also be used to infer types, check whether a
    type \c A is convertible to a type \c B, etc. */
class type_checker : public abstract_type_context {
    /* In the type checker cache, we must take into account binder information.
       Examples:
       The type of (lambda x : A, t)   is (Pi x : A, typeof(t))
       The type of (lambda {x : A}, t) is (Pi {x : A}, typeof(t)) */
    typedef expr_bi_map<expr> cache;
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> expr_pair_set;
    environment               m_env;
    name_generator            m_name_generator;
    bool                      m_memoize;
    bool                      m_trusted_only;
    cache                     m_infer_type_cache[2];
    expr_map<expr>            m_whnf_core_cache;
    expr_map<expr>            m_whnf_cache;
    equiv_manager             m_eqv_manager;
    expr_pair_set             m_failure_cache;
    level_param_names const * m_params;

    pair<expr, expr> open_binding_body(expr const & e);
    expr ensure_sort_core(expr e, expr const & s);
    expr ensure_pi_core(expr e, expr const & s);
    void check_level(level const & l, expr const & s);
    expr infer_constant(expr const & e, bool infer_only);
    expr infer_macro(expr const & e, bool infer_only);
    expr infer_lambda(expr const & e, bool infer_only);
    expr infer_pi(expr const & e, bool infer_only);
    expr infer_app(expr const & e, bool infer_only);
    expr infer_let(expr const & e, bool infer_only);
    expr infer_type_core(expr const & e, bool infer_only);
    expr infer_type(expr const & e);

    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };
    optional<expr> norm_ext(expr const & e);
    expr whnf_core(expr const & e);
    optional<declaration> is_delta(expr const & e) const;
    optional<expr> unfold_definition_core(expr const & e);
    optional<expr> unfold_definition(expr const & e);

    bool is_def_eq_binding(expr t, expr s);
    bool is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(levels const & ls1, levels const & ls2);
    lbool quick_is_def_eq(expr const & t, expr const & s, bool use_hash = false);
    bool is_def_eq_args(expr t, expr s);
    bool try_eta_expansion_core(expr const & t, expr const & s);
    bool try_eta_expansion(expr const & t, expr const & s) {
        return try_eta_expansion_core(t, s) || try_eta_expansion_core(s, t);
    }
    bool is_def_eq_app(expr const & t, expr const & s);
    bool is_def_eq_proof_irrel(expr const & t, expr const & s);
    bool failed_before(expr const & t, expr const & s) const;
    void cache_failure(expr const & t, expr const & s);
    reduction_status lazy_delta_reduction_step(expr & t_n, expr & s_n);
    lbool lazy_delta_reduction(expr & t_n, expr & s_n);
    bool is_def_eq_core(expr const & t, expr const & s);

public:
    /** \brief Create a type checker for the given environment.
       memoize: if true, then inferred types are memoized/cached */
    type_checker(environment const & env, bool memoize = true, bool trusted_only = true);
    ~type_checker();

    virtual environment const & env() const { return m_env; }

    virtual name next_name() { return m_name_generator.next(); }

    /** \brief Return the type of \c t.
        It does not check whether the input expression is type correct or not.
        The contract is: IF the input expression is type correct, then the inferred
        type is correct.
        Throw an exception if a type error is found. */
    virtual expr infer(expr const & t) { return infer_type(t); }

    /** \brief Type check the given expression, and return the type of \c t.
        Throw an exception if a type error is found.  */
    expr check(expr const & t, level_param_names const & ps);
    /** \brief Like \c check, but ignores undefined universes */
    expr check_ignore_undefined_universes(expr const & e);
    virtual expr check(expr const & t) { return check_ignore_undefined_universes(t); }

    virtual bool is_trusted_only() const { return m_trusted_only; }

    /** \brief Return true iff t is definitionally equal to s. */
    virtual bool is_def_eq(expr const & t, expr const & s);
    /** \brief Return true iff types of \c t and \c s are (may be) definitionally equal. */
    bool is_def_eq_types(expr const & t, expr const & s);
    /** \brief Return true iff t is a proposition. */
    bool is_prop(expr const & t);
    /** \brief Return the weak head normal form of \c t. */
    virtual expr whnf(expr const & t);
    /** \brief Return a Pi if \c t is convertible to a Pi type. Throw an exception otherwise.
        The argument \c s is used when reporting errors */
    expr ensure_pi(expr const & t, expr const & s);
    expr ensure_pi(expr const & t) { return ensure_pi(t, t); }
    /** \brief Mare sure type of \c e is a Pi, and return it. Throw an exception otherwise. */
    expr ensure_fun(expr const & e) {
        return ensure_pi(infer(e), e);
    }
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise.
        The argument \c s is used when reporting errors. */
    expr ensure_sort(expr const & t, expr const & s);
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise. */
    expr ensure_sort(expr const & t) { return ensure_sort(t, t); }
    /** \brief Mare sure type of \c e is a sort, and return it. Throw an exception otherwise. */
    expr ensure_type(expr const & e) {
        return ensure_sort(infer(e), e);
    }

    optional<expr> expand_macro(expr const & m);

    /** \brief Return a metavariable that may be stucking the \c e's reduction. */
    virtual optional<expr> is_stuck(expr const & e);

    template<typename F>
    typename std::result_of<F()>::type with_params(level_param_names const & ps, F && f) {
        flet<level_param_names const *> updt(m_params, &ps);
        return f();
    }
};

typedef std::shared_ptr<type_checker> type_checker_ref;

void check_no_metavar(environment const & env, name const & n, expr const & e, bool is_type);
void check_no_mlocal(environment const & env, name const & n, expr const & e, bool is_type);

/** \brief Type check the given declaration, and return a certified declaration if it is type correct.
    Throw an exception if the declaration is type incorrect. */
certified_declaration check(environment const & env, declaration const & d, bool immediately = false);

void initialize_type_checker();
void finalize_type_checker();
}
