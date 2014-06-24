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
typedef std::function<void(constraint const & c)> add_cnstr_fn;

/** \brief This handler always throw an exception (\c no_constraints_allowed_exception) when \c add_cnstr is invoked. */
add_cnstr_fn mk_no_contranint_fn();

/** \brief Exception used in \c no_constraint_handler. */
class no_constraints_allowed_exception : public exception {
public:
    no_constraints_allowed_exception();
    virtual exception * clone() const;
    virtual void rethrow() const;
};

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
    add_cnstr_fn               m_add_cnstr_fn;
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
    bool                       m_cache_cs;  // true if we should cache the constraints; false if we should send to m_add_cnstr_fn

    friend class converter; // allow converter to access the following methods
    name mk_fresh_name() { return m_gen.next(); }
    optional<expr> expand_macro(expr const & m);
    std::pair<expr, expr> open_binding_body(expr const & e);
    void add_cnstr(constraint const & c);
    bool meta_to_telescope(expr const & e, buffer<expr> & telescope);
    bool meta_to_telescope_core(expr const & e, buffer<expr> & telescope, buffer<optional<expr>> & locals);
    expr ensure_sort_core(expr e, expr const & s);
    expr ensure_pi_core(expr e, expr const & s);
    justification mk_let_mismatch_jst(expr const & e, expr const & val_type);
    justification mk_macro_jst(expr const & e);
    void check_level(level const & l, expr const & s);
    expr infer_type_core(expr const & e, bool infer_only);
    expr infer_type(expr const & e);
    extension_context & get_extension() { return m_tc_ctx; }
public:
    class scope {
        type_checker &   m_tc;
        unsigned         m_old_cs_size;
        bool             m_old_cache_cs;
        bool             m_keep;
    public:
        scope(type_checker & tc);
        ~scope();
        void keep();
    };

public:
    /**
       \brief Create a type checker for the given environment. The auxiliary names created by this
       type checker are based on the given name generator.

       memoize: if true, then inferred types are memoized/cached
    */
    type_checker(environment const & env, name_generator const & g, add_cnstr_fn const & h, std::unique_ptr<converter> && conv,
                 bool memoize = true);
    type_checker(environment const & env, name_generator const & g, add_cnstr_fn const & h, bool memoize = true):
        type_checker(env, g, h, mk_default_converter(env), memoize) {}
    /**
       \brief Similar to the previous constructor, but if a method tries to create a constraint, then an
       exception is thrown.
    */
    type_checker(environment const & env, name_generator const & g, std::unique_ptr<converter> && conv, bool memoize = true);
    type_checker(environment const & env, name_generator const & g, bool memoize = true):
        type_checker(env, g, mk_default_converter(env), memoize) {}
    type_checker(environment const & env);
    ~type_checker();

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

    /** \brief Create a backtracking point for cache and generated constraints. */
    void push();
    /** \brief Restore backtracking point. */
    void pop();
    /** \brief Return the number of backtracking points. */
    unsigned num_scopes() const;
};

/**
   \brief Type check the given declaration, and return a certified declaration if it is type correct.
   Throw an exception if the declaration is type incorrect.
*/
certified_declaration check(environment const & env, declaration const & d,
                            name_generator const & g, name_set const & extra_opaque = name_set(), bool memoize = true);
certified_declaration check(environment const & env, declaration const & d, name_set const & extra_opaque = name_set(), bool memoize = true);

/**
   \brief Create a justification for a application type mismatch,
   \c e is the application, \c fn_type and \c arg_type are the function and argument type.
*/
class app_delayed_justification : public delayed_justification {
    environment const & m_env;
    expr const & m_e;
    expr const & m_fn_type;
    expr const & m_arg_type;
    optional<justification> m_jst;
public:
    app_delayed_justification(environment const & env, expr const & e, expr const & f_type, expr const & a_type);
    virtual justification get();
};
}
