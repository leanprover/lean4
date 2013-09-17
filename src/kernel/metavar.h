/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/pair.h"
#include "util/pvector.h"
#include "kernel/expr.h"
#include "kernel/context.h"

namespace lean {
/**
   \brief Set of unification problems that need to be solved.
   It store two kinds of problems:
   1. <tt>ctx |- lhs == rhs</tt>
   2. <tt>ctx |- typeof(n) == t</tt>
   3. <tt>ctx |- t1 is_convertible_to t2</tt>
*/
class unification_problems {
public:
    virtual ~unification_problems() {}
    /**
       \brief Add a new unification problem of the form <tt>ctx |- lhs == rhs</tt>
    */
    virtual void add_eq(context const & ctx, expr const & lhs, expr const & rhs) = 0;
    /**
       \brief Add a new unification problem of the form <tt>ctx |- typeof(n) == t</tt>
    */
    virtual void add_type_of_eq(context const & ctx, expr const & n, expr const & t) = 0;
    /**
       \brief Add a new problem of the form <tt>ctx |- t1 is_convertible_to t2</tt>

       \remark <tt>ctx |- t1 == t2</tt> implies <tt>ctx |- t1 is_convertible_to t2</tt>
    */
    virtual void add_is_convertible(context const & ctx, expr const & t1, expr const & t2) = 0;
};

/**
   \brief Metavariable environment. It is essentially a mapping
   from metavariables to assignments and types.
*/
class metavar_env {
    struct data {
        expr    m_subst;
        expr    m_type;
        context m_ctx;
        data(context const & ctx):m_ctx(ctx) {}
        data(expr const & s, expr const & t, context const & ctx):m_subst(s), m_type(t), m_ctx(ctx) {}
    };
    pvector<data> m_env;
    unsigned      m_timestamp;
    void inc_timestamp();
public:
    metavar_env();

    /**
       \brief The timestamp is increased whenever the environment is updated by
       \c mk_metavar or \c assign.
    */
    unsigned get_timestamp() const { return m_timestamp; }

    /**
       \brief Create new metavariable in this environment.
    */
    expr mk_metavar(context const & ctx = context());

    /**
       \brief Return true if this environment contains a metavariable
       with id \c midx. That is, it has an entry of the form
       <tt>midx -> (s, t)</tt>.
    */
    bool contains(unsigned midx) const;

    /**
       \brief Return true if the metavariable with id \c midx is assigned in
       this environment.

       \pre contains(midx)
    */
    bool is_assigned(unsigned midx) const;

    /**
       \brief Return the substitution associated with the metavariable with id \c midx
       in this environment.
       If the metavariable is not assigned in this environment, then it returns the null
       expression.

       \pre contains(midx)
    */
    expr get_subst(unsigned midx) const;

    /**
       \brief Return the type of the metavariable with id \c midx in this environment.

       \remark A new metavariable may be created to represent the type of the input
       metavariable. When this happens, a new unification problem of the form
       <tt>typeof(m) = t</tt> is added to \c up, where \c m is the metavariable
       with id \c midx, and \c t is the result of this method.

       \pre contains(midx)
    */
    expr get_type(unsigned midx, unification_problems & up);

    /**
       \brief Assign the metavariable with id \c midx to the term \c t.

       \pre !is_assigned(midx)
    */
    void assign(unsigned midx, expr const & t);

    /**
       \brief Return true if this environment contains the given metavariable

       \pre is_metavar(m)
    */
    bool contains(expr const & m) const { return contains(metavar_idx(m)); }

    /**
       \pre contains(m)
    */
    bool is_assigned(expr const & m) const { return is_assigned(metavar_idx(m)); }

    /**
       \brief Return the substitution associated with the metavariable \c m.
       If \c m has a context ctx associated with it, then the substitution is
       'moved' to ctx.

       \pre contains(m)
    */
    expr get_subst(expr const & m) const;

    /**
       \brief Return the type of the given metavariable.
       If \c m has a context ctx associated with it, then the type is
       'moved' to ctx.

       \pre contains(m)
    */
    expr get_type(expr const & m, unification_problems & up);

    /**
       \brief Assign the metavariable \c m to \c t.
       The metavariable must not have a context associated with it.

       \pre contains(m)
       \pre !metavar_ctx(m)
       \pre !is_assigned(m)
    */
    void assign(expr const & m, expr const & t);
};

/**
   \brief Instantiate the metavariables occurring in \c e with the substitutions
   provided by \c env.
*/
expr instantiate_metavars(expr const & e, metavar_env const & env);

/**
    \brief Extend the context \c ctx with the entry <tt>lift:s:n</tt>
*/
meta_ctx add_lift(meta_ctx const & ctx, unsigned s, unsigned n);

/**
   \brief Add a lift:s:n operation to the context of the given metavariable.

   \pre is_metavar(m)
*/
expr add_lift(expr const & m, unsigned s, unsigned n);

/**
   \brief Add an inst:s:v operation to the context of the given metavariable.

   \pre is_metavar(m)
*/
expr add_inst(expr const & m, unsigned s, expr const & v);

/**
   \brief Extend the context \c ctx with the entry <tt>inst:s v</tt>
*/
meta_ctx add_inst(meta_ctx const & ctx, unsigned s, expr const & v);

/**
   \brief Return true iff the given metavariable has a non-empty
   context associated with it.

   \pre is_metavar(m)
*/
bool has_context(expr const & m);

/**
   \brief Return the same metavariable, but the head of the context is removed.

   \pre is_metavar(m)
   \pre has_context(m)
*/
expr pop_context(expr const & m);

/**
   \brief Return true iff \c e contains the metavariable with index \c midx.
   The substitutions in \c menv are taken into account.
*/
bool has_metavar(expr const & e, unsigned midx, metavar_env const & menv = metavar_env());
}
