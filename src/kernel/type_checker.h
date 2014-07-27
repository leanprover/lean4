/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <algorithm>
#include "util/name_generator.h"
#include "util/name_set.h"
#include "util/scoped_map.h"
#include "kernel/environment.h"
#include "kernel/constraint.h"
#include "kernel/converter.h"

namespace lean {

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
    typedef scoped_map<expr, expr, expr_hash, is_bi_equal_proc> cache;

    /** \brief Interface type_checker <-> macro & normalizer_extension */
    class type_checker_context : public extension_context {
        type_checker & m_tc;
    public:
        type_checker_context(type_checker & tc):m_tc(tc) {}
        virtual environment const & env() const { return m_tc.m_env; }
        virtual expr whnf(expr const & e) { return m_tc.whnf(e); }
        virtual bool is_def_eq(expr const & e1, expr const & e2, delayed_justification & j) { return m_tc.is_def_eq(e1, e2, j); }
        virtual expr infer_type(expr const & e) { return m_tc.infer_type(e); }
        virtual name mk_fresh_name() { return m_tc.m_gen.next(); }
        virtual void add_cnstr(constraint const & c) { m_tc.add_cnstr(c); }
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
    level_param_names          m_params;
    buffer<constraint>         m_cs;        // temporary cache of constraints
    unsigned                   m_cs_qhead;
    buffer<std::pair<unsigned, unsigned>> m_trail;

    friend class converter; // allow converter to access the following methods
    name mk_fresh_name() { return m_gen.next(); }
    optional<expr> expand_macro(expr const & m);
    std::pair<expr, expr> open_binding_body(expr const & e);
    void add_cnstr(constraint const & c);
    expr ensure_sort_core(expr e, expr const & s);
    expr ensure_pi_core(expr e, expr const & s);
    justification mk_macro_jst(expr const & e);
    void check_level(level const & l, expr const & s);
    expr infer_constant(expr const & e, bool infer_only);
    expr infer_macro(expr const & e, bool infer_only);
    expr infer_lambda(expr const & e, bool infer_only);
    expr infer_pi(expr const & e, bool infer_only);
    expr infer_app(expr const & e, bool infer_only);
    expr infer_type_core(expr const & e, bool infer_only);
    expr infer_type(expr const & e);
    void copy_constraints(unsigned qhead, buffer<constraint> & new_cnstrs);
    extension_context & get_extension() { return m_tc_ctx; }
    constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j);
public:
    /**
       \brief Create a type checker for the given environment. The auxiliary names created by this
       type checker are based on the given name generator.

       memoize: if true, then inferred types are memoized/cached
    */
    type_checker(environment const & env, name_generator const & g, std::unique_ptr<converter> && conv, bool memoize = true);
    type_checker(environment const & env, name_generator const & g, bool memoize = true):
        type_checker(env, g, mk_default_converter(env), memoize) {}
    type_checker(environment const & env);
    ~type_checker();

    environment const & env() const { return m_env; }
    name_generator mk_ngen() { return m_gen.mk_child(); }

    /**
       \brief Return the type of \c t.

       It does not check whether the input expression is type correct or not.
       The contract is: IF the input expression is type correct, then the inferred
       type is correct.
       Throw an exception if a type error is found.

       The result is meaningful only if the constraints sent to the
       constraint handler can be solved.
   */
    expr infer(expr const & t) { return infer_type(t); }
    /** \brief Infer \c t type and copy constraints associated with type inference to \c new_cnstrs */
    expr infer(expr const & t, buffer<constraint> & new_cnstrs);

    /**
       \brief Type check the given expression, and return the type of \c t.
       Throw an exception if a type error is found.

       The result is meaningful only if the constraints sent to the
       constraint handler can be solved.
    */
    expr check(expr const & t, level_param_names const & ps = level_param_names());
    /** \brief Return true iff t is definitionally equal to s. */
    bool is_def_eq(expr const & t, expr const & s);
    bool is_def_eq(expr const & t, expr const & s, justification const & j);
    bool is_def_eq(expr const & t, expr const & s, delayed_justification & jst);
    /** \brief Return true iff \c t and \c s are (may be) definitionally equal (module constraints)
        New constraints associated with test are store in \c new_cnstrs.
    */
    bool is_def_eq(expr const & t, expr const & s, justification const & j, buffer<constraint> & new_cnstrs);
    /** \brief Return true iff types of \c t and \c s are (may be) definitionally equal (modulo constraints)
        New constraints associated with test are store in \c new_cnstrs.
    */
    bool is_def_eq_types(expr const & t, expr const & s, justification const & j, buffer<constraint> & new_cnstrs);
    /** \brief Return true iff t is a proposition. */
    bool is_prop(expr const & t);
    /** \brief Return the weak head normal form of \c t. */
    expr whnf(expr const & t);
    /** \brief Similar to the previous method, but it also returns the new constraints created in the process. */
    expr whnf(expr const & t, buffer<constraint> & new_cnstrs);
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

    /** \brief Return the number of backtracking points. */
    unsigned num_scopes() const;
    /** \brief Consume next constraint in the produced constraint queue */
    optional<constraint> next_cnstr();

    void push();
    void pop();
    void keep();

    class scope {
        type_checker &   m_tc;
        bool             m_keep;
    public:
        scope(type_checker & tc);
        ~scope();
        void keep();
    };
};

/**
   \brief Type check the given declaration, and return a certified declaration if it is type correct.
   Throw an exception if the declaration is type incorrect.
*/
certified_declaration check(environment const & env, declaration const & d,
                            name_generator const & g, name_set const & extra_opaque = name_set(), bool memoize = true);
certified_declaration check(environment const & env, declaration const & d, name_set const & extra_opaque = name_set(), bool memoize = true);

/**
    \brief Create a justification for an application \c e where the expected type must be \c d_type and
    the argument type is \c a_type.
*/
justification mk_app_justification(expr const & e, expr const & d_type, expr const & a_type);

/**
   \brief Create a justification for a application type mismatch,
   \c e is the application, \c fn_type and \c arg_type are the function and argument type.
*/
class app_delayed_justification : public delayed_justification {
    expr const & m_e;
    expr const & m_fn_type;
    expr const & m_arg_type;
    optional<justification> m_jst;
public:
    app_delayed_justification(expr const & e, expr const & f_type, expr const & a_type);
    virtual justification get();
};
}
