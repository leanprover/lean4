/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <algorithm>
#include "util/flet.h"
#include "util/name_generator.h"
#include "util/name_set.h"
#include "kernel/environment.h"
#include "kernel/constraint.h"
#include "kernel/justification.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"

namespace lean {
/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type);

inline pair<expr, constraint_seq> to_ecs(expr const & e) { return mk_pair(e, empty_cs()); }
inline pair<expr, constraint_seq> to_ecs(expr const & e, constraint const & c, constraint_seq const & cs) {
    return mk_pair(e, constraint_seq(constraint_seq(c), cs));
}
inline pair<expr, constraint_seq> to_ecs(expr const & e, constraint const & c) { return mk_pair(e, constraint_seq(c)); }
inline pair<expr, constraint_seq> to_ecs(expr const & e, constraint_seq const & cs) { return mk_pair(e, cs); }

/** \brief Given \c type of the form <tt>(Pi ctx, r)</tt>, return <tt>(Pi ctx, new_range)</tt> */
expr replace_range(expr const & type, expr const & new_range);

/**
   \brief Given a type \c t of the form
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
   return a new metavariable \c m1 with type
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{u}</tt>
   where \c u is a new universe metavariable.
*/
expr mk_aux_type_metavar_for(name_generator & ngen, expr const & t);

/**
   \brief Given a type \c t of the form
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
   return a new metavariable \c m1 with type
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), (?m2 x_1 ... x_n)</tt>
   where \c ?m2 is a new metavariable with type
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{u}</tt>
   where \c u is a new universe metavariable.
*/
expr mk_aux_metavar_for(name_generator & ngen, expr const & t);

/**
   \brief Given a meta (?m t_1 ... t_n) where ?m has type
      <tt>Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), B[x_1, ..., x_n]</tt>
   return a Pi term
      <tt>Pi (x : ?m1 t_1 ... t_n), (?m2 t_1 ... t_n x) </tt>
   where ?m1 and ?m2 are fresh metavariables
*/
expr mk_pi_for(name_generator & ngen, expr const & meta);

/**
   \brief Lean Type Checker. It can also be used to infer types, check whether a
   type \c A is convertible to a type \c B, etc.

   The type checker produces constraints, and they are sent to the constraint handler.
*/
class type_checker {
    typedef expr_bi_struct_map<pair<expr, constraint_seq>> cache;

    /** \brief Interface type_checker <-> macro & normalizer_extension */
    class type_checker_context : public extension_context {
        type_checker & m_tc;
    public:
        type_checker_context(type_checker & tc):m_tc(tc) {}
        virtual environment const & env() const { return m_tc.m_env; }
        virtual pair<expr, constraint_seq> whnf(expr const & e) { return m_tc.whnf(e); }
        virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification & j) {
            return m_tc.is_def_eq(e1, e2, j);
        }
        virtual pair<expr, constraint_seq> check_type(expr const & e, bool infer_only) {
            return m_tc.infer_type_core(e, infer_only);
        }
        virtual name mk_fresh_name() { return m_tc.m_gen.next(); }
        virtual optional<expr> is_stuck(expr const & e) { return m_tc.is_stuck(e); }
    };

    environment                m_env;
    name_generator             m_gen;
    std::unique_ptr<converter> m_conv;
    // In the type checker cache, we must take into account binder information.
    // Examples:
    // The type of (lambda x : A, t)   is (Pi x : A, typeof(t))
    // The type of (lambda {x : A}, t) is (Pi {x : A}, typeof(t))
    cache                      m_infer_type_cache[2];
    type_checker_context       m_tc_ctx;
    bool                       m_memoize;
    // temp flag
    level_param_names const *  m_params;

    friend class converter; // allow converter to access the following methods
    pair<expr, expr> open_binding_body(expr const & e);
    pair<expr, constraint_seq> ensure_sort_core(expr e, expr const & s);
    pair<expr, constraint_seq> ensure_pi_core(expr e, expr const & s);
    justification mk_macro_jst(expr const & e);
    void check_level(level const & l, expr const & s);
    expr infer_constant(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_macro(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_lambda(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_pi(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_app(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_type_core(expr const & e, bool infer_only);
    pair<expr, constraint_seq> infer_type(expr const & e);
    expr infer_type_core(expr const & e, bool infer_only, constraint_seq & cs);

    extension_context & get_extension() { return m_tc_ctx; }
    constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j);
public:
    /**
       \brief Create a type checker for the given environment. The auxiliary names created by this
       type checker are based on the given name generator.

       memoize: if true, then inferred types are memoized/cached
    */
    type_checker(environment const & env, name_generator && g, std::unique_ptr<converter> && conv, bool memoize = true);
    type_checker(environment const & env, name_generator && g, bool memoize = true);
    type_checker(environment const & env);
    ~type_checker();

    environment const & env() const { return m_env; }
    name_generator mk_ngen() { return m_gen.mk_child(); }
    name mk_fresh_name() { return m_gen.next(); }
    /**
       \brief Return the type of \c t.

       It does not check whether the input expression is type correct or not.
       The contract is: IF the input expression is type correct, then the inferred
       type is correct.
       Throw an exception if a type error is found.

       The result is meaningful only if the generated constraints can be solved.
   */
    pair<expr, constraint_seq> infer(expr const & t) { return infer_type(t); }

    /**
       \brief Type check the given expression, and return the type of \c t.
       Throw an exception if a type error is found.

       The result is meaningful only if the generated constraints can be solved.
    */
    pair<expr, constraint_seq> check(expr const & t, level_param_names const & ps = level_param_names());
    /** \brief Like \c check, but ignores undefined universes */
    pair<expr, constraint_seq> check_ignore_undefined_universes(expr const & e);

    /** \brief Return true iff t is definitionally equal to s. */
    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s);
    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, justification const & j);
    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, delayed_justification & jst);
    /** \brief Return true iff types of \c t and \c s are (may be) definitionally equal (modulo constraints) */
    pair<bool, constraint_seq> is_def_eq_types(expr const & t, expr const & s, justification const & j);
    /** \brief Return true iff t is a proposition. */
    pair<bool, constraint_seq> is_prop(expr const & t);
    /** \brief Return the weak head normal form of \c t. */
    pair<expr, constraint_seq> whnf(expr const & t);
    /** \brief Return a Pi if \c t is convertible to a Pi type. Throw an exception otherwise.
        The argument \c s is used when reporting errors */
    pair<expr, constraint_seq> ensure_pi(expr const & t, expr const & s);
    pair<expr, constraint_seq> ensure_pi(expr const & t) { return ensure_pi(t, t); }
    /** \brief Mare sure type of \c e is a Pi, and return it. Throw an exception otherwise. */
    pair<expr, constraint_seq> ensure_fun(expr const & e) {
        auto tcs  = infer(e);
        auto pics = ensure_pi(tcs.first, e);
        return mk_pair(pics.first, pics.second + tcs.second);
    }
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise.
        The argument \c s is used when reporting errors. */
    pair<expr, constraint_seq> ensure_sort(expr const & t, expr const & s);
    /** \brief Return a Sort if \c t is convertible to Sort. Throw an exception otherwise. */
    pair<expr, constraint_seq> ensure_sort(expr const & t) { return ensure_sort(t, t); }
    /** \brief Mare sure type of \c e is a sort, and return it. Throw an exception otherwise. */
    pair<expr, constraint_seq> ensure_type(expr const & e) {
        auto tcs = infer(e);
        auto scs = ensure_sort(tcs.first, e);
        return mk_pair(scs.first, scs.second + tcs.second);
    }

    expr whnf(expr const & e, constraint_seq & cs) { auto r = whnf(e); cs += r.second; return r.first; }
    expr infer(expr const & e, constraint_seq & cs) { auto r = infer(e); cs += r.second; return r.first; }
    expr ensure_pi(expr const & e, constraint_seq & cs) { auto r = ensure_pi(e); cs += r.second; return r.first; }
    expr ensure_pi(expr const & e, expr const & s, constraint_seq & cs) { auto r = ensure_pi(e, s); cs += r.second; return r.first; }
    expr ensure_sort(expr const & t, expr const & s, constraint_seq & cs) { auto r = ensure_sort(t, s); cs += r.second; return r.first; }
    expr ensure_type(expr const & e, constraint_seq & cs) { auto r = ensure_type(e); cs += r.second; return r.first; }

    bool is_def_eq(expr const & t, expr const & s, justification const & j, constraint_seq & cs) {
        auto r = is_def_eq(t, s, j);
        if (r.first)
            cs = r.second + cs;
        return r.first;
    }

    bool is_def_eq_types(expr const & t, expr const & s, justification const & j, constraint_seq & cs) {
        auto r = is_def_eq_types(t, s, j);
        if (r.first)
            cs = r.second + cs;
        return r.first;
    }

    optional<expr> expand_macro(expr const & m);

    /** \brief Return true iff \c d is opaque with respect to this type checker. */
    bool is_opaque(declaration const & d) const;
    /** \brief Return true iff the constant \c c is opaque with respect to this type checker. */
    bool is_opaque(expr const & c) const;

    /** \brief Return a metavariable that may be stucking the \c e's reduction. */
    optional<expr> is_stuck(expr const & e);

    optional<declaration> is_delta(expr const & e) const { return m_conv->is_delta(e); }

    bool may_reduce_later(expr const & e) { return m_conv->is_stuck(e, *this); }

    template<typename F>
    typename std::result_of<F()>::type with_params(level_param_names const & ps, F && f) {
        flet<level_param_names const *> updt(m_params, &ps);
        return f();
    }
};

typedef std::shared_ptr<type_checker> type_checker_ref;

void check_no_metavar(environment const & env, name const & n, expr const & e, bool is_type);

/**
   \brief Type check the given declaration, and return a certified declaration if it is type correct.
   Throw an exception if the declaration is type incorrect.
*/
certified_declaration check(environment const & env, declaration const & d, name_generator && g);
certified_declaration check(environment const & env, declaration const & d);

/**
    \brief Create a justification for an application \c e where the expected type must be \c d_type and
    the argument type is \c a_type.
*/
justification mk_app_justification(expr const & e, expr const & arg, expr const & d_type, expr const & a_type);

/**
   \brief Create a justification for a application type mismatch,
   \c e is the application, \c fn_type and \c arg_type are the function and argument type.
*/
class app_delayed_justification : public delayed_justification {
    expr const & m_e;
    expr const & m_arg;
    expr const & m_fn_type;
    expr const & m_arg_type;
    optional<justification> m_jst;
public:
    app_delayed_justification(expr const & e, expr const & arg, expr const & f_type, expr const & a_type);
    virtual justification get();
};

void initialize_type_checker();
void finalize_type_checker();
}
