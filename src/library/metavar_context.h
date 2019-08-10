/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/local_context.h"

namespace lean {
class metavar_decl {
    name          m_user_name;
    local_context m_context;
    expr          m_type;
    friend class metavar_context;
    metavar_decl(name const & user_name, local_context const & ctx, expr const & type):
        m_user_name(user_name), m_context(ctx), m_type(type) {}
public:
    metavar_decl() {}
    expr const & get_type() const { return m_type; }
    local_context const & get_context() const { return m_context; }
    name const & get_user_name() const { return m_user_name; }
};

bool is_metavar_decl_ref(level const & l);
bool is_metavar_decl_ref(expr const & e);

name get_metavar_decl_ref_suffix(level const & l);
name get_metavar_decl_ref_suffix(expr const & e);

class metavar_context {
    class delayed_assignment : public object_ref {
    public:
        delayed_assignment();
        delayed_assignment(local_context const & lctx, exprs const & locals, expr const & v);
        delayed_assignment(delayed_assignment const & other):object_ref(other) {}
        delayed_assignment(delayed_assignment && other):object_ref(other) {}
        delayed_assignment & operator=(delayed_assignment const & other) { object_ref::operator=(other); return *this; }
        delayed_assignment & operator=(delayed_assignment && other) { object_ref::operator=(other); return *this; }
        local_context const & get_lctx() const { return static_cast<local_context const &>(cnstr_get_ref(raw(), 0)); }
        exprs const & get_locals() const { return static_cast<exprs const &>(cnstr_get_ref(raw(), 1)); }
        expr const & get_val() const { return static_cast<expr const &>(cnstr_get_ref(raw(), 2)); }
    };

    name_map<metavar_decl>       m_decls;
    name_map<level>              m_uassignment;
    name_map<expr>               m_eassignment;
    name_map<delayed_assignment> m_dassignment;

    struct interface_impl;
    friend struct interface_impl;
public:
    level mk_univ_metavar_decl();

    expr mk_metavar_decl(name const & user_name, local_context const & ctx, expr const & type);

    expr mk_metavar_decl(local_context const & ctx, expr const & type) {
        return mk_metavar_decl(name(), ctx, type);
    }

    optional<metavar_decl> find_metavar_decl(expr const & mvar) const;

    metavar_decl const & get_metavar_decl(expr const & mvar) const;

    /** \brief Return the local_decl for `n` in the local context for the metavariable `mvar`
        \pre is_metavar(mvar) */
    optional<local_decl> find_local_decl(expr const & mvar, name const & n) const;

    local_decl get_local_decl(expr const & mvar, name const & n) const;

    /** \brief Return the local_decl_ref for `n` in the local context for the metavariable `mvar`

        \pre is_metavar(mvar)
        \pre find_metavar_decl(mvar)
        \pre find_metavar_decl(mvar)->get_context().get_local_decl(n) */
    expr get_local(expr const & mvar, name const & n) const;

    bool is_assigned(level const & l) const {
        lean_assert(is_metavar_decl_ref(l));
        return m_uassignment.contains(mvar_id(l));
    }

    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar_decl_ref(m));
        return m_eassignment.contains(mvar_name(m));
    }

    bool is_delayed_assigned(expr const & m) const {
        lean_assert(is_metavar_decl_ref(m));
        return m_dassignment.contains(mvar_name(m));
    }

    void assign(level const & u, level const & l);
    void assign(expr const & e, expr const & v);
    /*
      Add the delayed assignment
      ```
      e := Fun(locals, v)
      ```
      This kind of assignment is created by the `intro` tactic.
      The term `v` contains metavariables that have not been instantiated yet.
      So, `abstract_locals(locals, v)` would not work correctly.
      We also cannot create an auxiliary metavariable in this case since it would "solve" the new goal
      created by the `intro` tactic.

      \pre is_metavar_decl_ref(e)
    */
    void assign(expr const & e, local_context const & lctx, exprs const & locals, expr const & v);

    level instantiate_mvars(level const & l);
    expr instantiate_mvars(expr const & e);

    bool has_assigned(level const & l) const;
    bool has_assigned(levels const & ls) const;
    bool has_assigned(expr const & e) const;

    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    optional<delayed_assignment> get_delayed_assignment(expr const & e) const;

    /** \brief Instantiate the assigned meta-variables in the type of \c m
        \pre get_metavar_decl(m) is not none */
    void instantiate_mvars_at_type_of(expr const & m);

    /** \brief Return true iff \c ctx is well-formed with respect to this metavar context.
        That is, every metavariable ?M occurring in \c ctx is declared here, and
        for every metavariable ?M occurring in a declaration \c d, the context of ?M
        must be a subset of the declarations declared *before* \c d.

        \remark This method is used for debugging purposes. */
    bool well_formed(local_context const & ctx) const;

    /** \brief Return true iff all metavariables ?M in \c e are declared in this metavar context,
        and context of ?M is a subset of \c ctx */
    bool well_formed(local_context const & ctx, expr const & e) const;
};

/** \brief Check whether the local context lctx is well-formed and well-formed with respect to \c mctx.
    \remark This procedure is used for debugging purposes. */
bool well_formed(local_context const & lctx, metavar_context const & mctx);

/** \brief Check whether \c e is well-formed with respect to \c lctx and \c mctx. */
bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e);

void initialize_metavar_context();
void finalize_metavar_context();
}
