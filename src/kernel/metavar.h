/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/pair.h"
#include "util/splay_map.h"
#include "util/name_generator.h"
#include "kernel/expr.h"
#include "kernel/context.h"

namespace lean {
/**
   \brief Metavariable substitution. It is essentially a mapping from
   metavariables to expressions.
*/
class substitution {
    typedef splay_map<name, expr, name_cmp> name2expr;
    name2expr m_subst;
    unsigned  m_size;
    unsigned  m_timestamp;

    void inc_timestamp();
public:
    substitution();

    /**
       \brief The timestamp is increased whenever the substitution is updated by
       \c mk_metavar or \c assign.
    */
    unsigned get_timestamp() const { return m_timestamp; }

    /**
       \brief Return the number of assigned metavariables in this substitution.
    */
    unsigned size() const { return m_size; }

    /**
       \brief Return true iff the metavariable named \c m is assigned in this substitution.
    */
    bool is_assigned(name const & m) const;

    /**
       \brief Return true if the given metavariable is assigned in this
       substitution.

       \pre is_metavar(m)
    */
    bool is_assigned(expr const & m) const;

    /**
       \brief Assign metavariable named \c m.

       \pre !is_assigned(m)
    */
    void assign(name const & m, expr const & t);

    /**
       \brief Assign metavariable \c m to \c t.

       \pre is_metavar(m)
       \pre !has_meta_context(m)
       \pre !is_assigned(m)
    */
    void assign(expr const & m, expr const & t);

    /**
       \brief Return the substitution associated with the given metavariable
       in this substitution.

       If the metavariable is not assigned in this substitution, then it returns the null
       expression.

       \pre is_metavar(m)
    */
    expr get_subst(expr const & m) const;

    bool operator==(substitution const & s) const;
    bool operator!=(substitution const & s) const { return !operator==(s); }

    /**
       \brief Apply f to each entry in this substitution.
    */
    template<typename F>
    void for_each(F f) const { m_subst.for_each(f); }
};

/**
   \brief Metavar environment. It is an auxiliary datastructure used for:

   1- Creating metavariables.
   2- Storing their types and the contexts where they were created.
   3- Storing substitutions.
   4- Collecting constraints
*/
class metavar_env {
    typedef splay_map<name, expr, name_cmp> name2expr;
    typedef splay_map<name, context, name_cmp> name2context;

    name_generator m_name_generator;
    substitution   m_substitution;
    name2expr      m_metavar_types;
    name2context   m_metavar_contexts;
    unsigned       m_timestamp;

    void inc_timestamp();
public:
    metavar_env();

    /**
       \brief The timestamp is increased whenever this environment is
       updated.
    */
    unsigned get_timestamp() const { return m_timestamp; }

    /**
       \brief Create a new metavariable in the given context and with the given type.
    */
    expr mk_metavar(context const & ctx = context(), expr const & type = expr());

    /**
       \brief Return the context where the given metavariable was created.
       \pre is_metavar(m)
    */
    context get_context(expr const & m);
    context get_context(name const & m);

    /**
       \brief Return the type of the given metavariable.
       \pre is_metavar(m)
    */
    expr get_type(expr const & m);
    expr get_type(name const & m);

    /**
       \brief Return true iff the metavariable named \c m is assigned in this substitution.
    */
    bool is_assigned(name const & m) const;

    /**
       \brief Return true if the given metavariable is assigned in this
       substitution.

       \pre is_metavar(m)
    */
    bool is_assigned(expr const & m) const;

    /**
       \brief Assign metavariable named \c m.

       \pre !is_assigned(m)
    */
    void assign(name const & m, expr const & t);

    /**
       \brief Assign metavariable \c m to \c t.

       \pre is_metavar(m)
       \pre !has_meta_context(m)
       \pre !is_assigned(m)
    */
    void assign(expr const & m, expr const & t);

    /**
       \brief Return the set of substitutions.
    */
    substitution const & get_substitutions() const;

    /**
       \brief Return the substitution associated with the given metavariable
       in this substitution.

       If the metavariable is not assigned in this substitution, then it returns the null
       expression.

       \pre is_metavar(m)
    */
    expr get_subst(expr const & m) const;
};

/**
   \brief Metavar generator.
*/
class metavar_generator {
    name_generator m_gen;
public:
    metavar_generator(name const & prefix);
    metavar_generator();

    /**
       \brief Return the prefix used to create metavariables in this generator.
    */
    name const & prefix() const { return m_gen.prefix(); }

    /**
       \brief Create a metavariable with the given type.
    */
    expr mk(expr const & t);

    /**
       \brief Create a metavariable where the type is another
       metavariable. The type of the type is a null expression.
    */
    expr mk();
};

/**
   \brief Apply the changes in \c lctx to \c a.
*/
expr apply_local_context(expr const & a, local_context const & lctx);

/**
   \brief Instantiate the metavariables occurring in \c e with the substitutions
   provided by \c s.
*/
expr instantiate_metavars(expr const & e, substitution const & s);

/**
    \brief Extend the local context \c lctx with the entry <tt>lift:s:n</tt>
*/
local_context add_lift(local_context const & lctx, unsigned s, unsigned n);

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
   \brief Extend the local context \c lctx with the entry <tt>inst:s v</tt>
*/
local_context add_inst(local_context const & lctx, unsigned s, expr const & v);

/**
   \brief Return true iff the given metavariable has a non-empty
   local context associated with it.

   \pre is_metavar(m)
*/
bool has_local_context(expr const & m);

/**
   \brief Return the same metavariable, but the head of the context is removed.

   \pre is_metavar(m)
   \pre has_meta_context(m)
*/
expr pop_meta_context(expr const & m);

/**
   \brief Return true iff \c e has a metavariable that is assigned in \c s.
*/
bool has_assigned_metavar(expr const & e, substitution const & s);

/**
   \brief Return true iff \c e contains the metavariable \c m.
   The substitutions in \c s are taken into account.

   \brief is_metavar(m)
*/
bool has_metavar(expr const & e, expr const & m, substitution const & s = substitution());


/**
   \brief Set of unification constraints that need to be solved.
   It store two kinds of problems:
   1. <tt>ctx |- lhs == rhs</tt>
   2. <tt>ctx |- n : t</tt>
*/
class unification_constraints {
public:
    virtual ~unification_constraints() {}
    /**
       \brief Add a new unification problem of the form <tt>ctx |- lhs == rhs</tt>
       It means that rhs is convertible to lhs.
       If rhs and lhs are not types, then this is just equality (modulo normalization).
    */
    virtual void add(context const & ctx, expr const & lhs, expr const & rhs) = 0;
    /**
       \brief Add a new unification problem of the form <tt>ctx |- n : t</tt>
    */
    virtual void add_type_of(context const & ctx, expr const & n, expr const & t) = 0;
};
}
