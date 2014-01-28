/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/rc.h"
#include "util/pair.h"
#include "util/splay_map.h"
#include "util/name_generator.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/justification.h"
#include "kernel/replace_visitor.h"

namespace lean {
/**
   \brief Metavar environment (cell). It is an auxiliary datastructure used for:

   1- Creating metavariables.
   2- Storing their types and the contexts where they were created.
   3- Storing substitutions.
*/
class metavar_env_cell {
    friend class metavar_env;
    struct data {
        optional<expr> m_subst;         // substitution
        optional<expr> m_type;          // type of the metavariable
        context        m_context;       // context where the metavariable was defined
        justification  m_justification; // justification for assigned metavariables.
        data(optional<expr> const & t = none_expr(), context const & ctx = context()):m_type(t), m_context(ctx) {}
    };
    typedef splay_map<name, data, name_quick_cmp> name2data;

    name_generator     m_name_generator;
    name2data          m_metavar_data;
    // If the following flag is true, then beta-reduction is automatically applied
    // when we apply a substitution containing ?m <- fun (x : T), ...
    // to an expression containing (?m a)
    // The motivation is that higher order unification and matching produces a
    // bunch of assignments of the form ?m <- fun (x : T), ...
    bool               m_beta_reduce_mv;
    unsigned           m_timestamp;
    MK_LEAN_RC();

    static bool has_metavar(expr const & e) { return ::lean::has_metavar(e); }
    void dealloc() { delete this; }
    void inc_timestamp();
public:
    metavar_env_cell();
    metavar_env_cell(name const & prefix);
    metavar_env_cell(metavar_env_cell const & other);

    bool beta_reduce_metavar_application() const { return m_beta_reduce_mv; }
    void set_beta_reduce_metavar_application(bool f) { m_beta_reduce_mv = f; }

    /**
       \brief The timestamp is increased whenever this environment is
       updated.

       \remark The result is always greater than 0.
    */
    unsigned get_timestamp() const { return m_timestamp; }

    /**
       \brief Create a new metavariable in the given context and with the given type.
    */
    expr mk_metavar(context const & ctx = context(), optional<expr> const & type = none_expr());

    /**
       \brief Return the context where the given metavariable was created.
       \pre is_metavar(m)
       \pre !has_local_context(m)
    */
    context get_context(expr const & m) const;
    context get_context(name const & m) const;

    unsigned get_context_size(expr const & m) const { return get_context(m).size(); }
    unsigned get_context_size(name const & m) const { return get_context(m).size(); }

    /**
       \brief Return the type of the given metavariable.
       \pre is_metavar(m)

       \remark If \c m does not have a type associated with it, then a new
       metavariable is created to represent the type of \c m.

       \remark If \c m has a local context, then the local context is applied.
    */
    expr get_type(expr const & m);
    expr get_type(name const & m);

    /**
        \brief Return true iff \c m has a type associated with it.
        \pre is_metavar(m)
    */
    bool has_type(expr const & m) const;
    bool has_type(name const & m) const;

    /**
       \brief Return the substitution and justification for the given metavariable.
    */
    optional<std::pair<expr, justification>> get_subst_jst(name const & m) const;
    optional<std::pair<expr, justification>> get_subst_jst(expr const & m) const;

    /**
       \brief Return the justification for an assigned metavariable.
       \pre is_metavar(m)
    */
    optional<justification> get_justification(expr const & m) const;
    optional<justification> get_justification(name const & m) const;

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

       \remark The method returns false if the assignment cannot be performed
       because \c t contain free variables that are not available in the context
       associated with \c m.
    */
    bool assign(name const & m, expr const & t, justification const & j);
    bool assign(name const & m, expr const & t);

    /**
       \brief Assign metavariable \c m to \c t.

       \remark The method returns false if the assignment cannot be performed
       because \c t contain free variables that are not available in the context
       associated with \c m.

       \pre is_metavar(m)
       \pre !has_meta_context(m)
       \pre !is_assigned(m)
    */
    bool assign(expr const & m, expr const & t, justification const & j);
    bool assign(expr const & m, expr const & t);

    /**
       \brief Return the substitution associated with the given metavariable
       in this substitution.

       \pre is_metavar(m)
    */
    optional<expr> get_subst(expr const & m) const;
    optional<expr> get_subst(name const & m) const;

    /**
       \brief Apply f to each substitution in the metavariable environment.
    */
    template<typename F>
    void for_each_subst(F f) const {
        m_metavar_data.for_each([&](name const & k, data const & d) {
                if (d.m_subst)
                    f(k, *(d.m_subst));
            });
    }

    /**
       \brief Return true iff \c e has a metavariable that is assigned in \c menv.
    */
    bool has_assigned_metavar(expr const & e) const;

    /**
       \brief Return true iff \c e contains the metavariable \c m.
       The substitutions in this metavar environment are taken into account.

       \brief is_metavar(m)
    */
    bool has_metavar(expr const & e, expr const & m) const;

   /**
      \brief Instantiate the metavariables occurring in \c e with the substitutions
      provided by \c menv. Store the justification of replace variables in jsts.
   */
    expr instantiate_metavars(expr const & e, buffer<justification> & jsts) const;
    inline expr instantiate_metavars(expr const & e) const {
        buffer<justification> tmp;
        return instantiate_metavars(e, tmp);
    }
    context instantiate_metavars(context const & ctx) const;
};

class ro_metavar_env;
/**
   \brief Reference to metavariable environment (cell).
*/
class metavar_env {
    friend class optional<metavar_env>;
    friend class ro_metavar_env;
    friend class metavar_env_cell;
    metavar_env_cell * m_ptr;
    explicit metavar_env(metavar_env_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    friend class type_checker;
    explicit metavar_env(ro_metavar_env const & s);
public:
    metavar_env():m_ptr(new metavar_env_cell()) { m_ptr->inc_ref(); }
    metavar_env(name const & prefix):m_ptr(new metavar_env_cell(prefix)) { m_ptr->inc_ref(); }
    metavar_env(metavar_env const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    metavar_env(metavar_env && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~metavar_env() { if (m_ptr) m_ptr->dec_ref(); }
    metavar_env & operator=(metavar_env const & s) { LEAN_COPY_REF(s); }
    metavar_env & operator=(metavar_env && s) { LEAN_MOVE_REF(s); }
    metavar_env_cell * operator->() const { return m_ptr; }
    metavar_env_cell & operator*() const { return *m_ptr; }
    metavar_env copy() const { return metavar_env(new metavar_env_cell(*m_ptr)); }
    friend bool is_eqp(metavar_env const & menv1, metavar_env const & menv2) { return menv1.m_ptr == menv2.m_ptr; }
    friend bool operator==(metavar_env const & menv1, metavar_env const & menv2) { return is_eqp(menv1, menv2); }
};

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(metavar_env)
inline optional<metavar_env> none_menv() { return optional<metavar_env>(); }
inline optional<metavar_env> some_menv(metavar_env const & e) { return optional<metavar_env>(e); }
inline optional<metavar_env> some_menv(metavar_env && e) { return optional<metavar_env>(std::forward<metavar_env>(e)); }

inline expr instantiate_metavars(optional<metavar_env> const & menv, expr const & e) {
    if (menv)
        return (*menv)->instantiate_metavars(e);
    else
        return e;
}

inline context instantiate_metavars(optional<metavar_env> const & menv, context const & ctx) {
    if (menv)
        return (*menv)->instantiate_metavars(ctx);
    else
        return ctx;
}

/**
   \brief Read-only reference to metavariable environment (cell).
*/
class ro_metavar_env {
    friend class optional<ro_metavar_env>;
    friend class metavar_env;
    metavar_env_cell * m_ptr;
    explicit ro_metavar_env(metavar_env_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
public:
    ro_metavar_env():m_ptr(new metavar_env_cell()) { m_ptr->inc_ref(); }
    ro_metavar_env(metavar_env const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    ro_metavar_env(ro_metavar_env const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    ro_metavar_env(ro_metavar_env && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~ro_metavar_env() { if (m_ptr) m_ptr->dec_ref(); }
    ro_metavar_env & operator=(ro_metavar_env const & s) { LEAN_COPY_REF(s); }
    ro_metavar_env & operator=(ro_metavar_env && s) { LEAN_MOVE_REF(s); }
    metavar_env_cell const * operator->() const { return m_ptr; }
    metavar_env_cell const & operator*() const { return *m_ptr; }
    metavar_env copy() const { return metavar_env(new metavar_env_cell(*m_ptr)); }
    friend bool is_eqp(ro_metavar_env const & menv1, ro_metavar_env const & menv2) { return menv1.m_ptr == menv2.m_ptr; }
    friend bool operator==(ro_metavar_env const & menv1, ro_metavar_env const & menv2) { return is_eqp(menv1, menv2); }
};

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(ro_metavar_env)
inline optional<ro_metavar_env> none_ro_menv() { return optional<ro_metavar_env>(); }
inline optional<ro_metavar_env> some_ro_menv(ro_metavar_env const & e) { return optional<ro_metavar_env>(e); }
inline optional<ro_metavar_env> some_ro_menv(ro_metavar_env && e) { return optional<ro_metavar_env>(std::forward<ro_metavar_env>(e)); }
inline optional<ro_metavar_env> const & to_ro_menv(optional<metavar_env> const & menv) { return reinterpret_cast<optional<ro_metavar_env> const &>(menv); }

/**
   \brief A cached weak reference to a metavariable environment + timestamp at the time of
   the caching. This object may also cache optional references.
*/
class cached_metavar_env {
    optional<metavar_env> m_menv;
    unsigned              m_timestamp;
public:
    cached_metavar_env():m_timestamp(0) {}
    void clear() { m_menv = none_menv(); m_timestamp = 0; }
    /**
       \brief Updated the cached value with menv.
       Return true if menv is different from the the cached metavar_env, or if
       the timestamp is different.
    */
    bool update(optional<metavar_env> const & menv);
    bool update(metavar_env const & menv) { return update(some(menv)); }
    explicit operator bool() const { return static_cast<bool>(m_menv); }
    optional<metavar_env> const & to_some_menv() const { return m_menv; }
    optional<ro_metavar_env> const & to_some_ro_menv() const { return to_ro_menv(m_menv); }
    metavar_env operator*() const { return *m_menv; }
    metavar_env_cell * operator->() const { lean_assert(m_menv); return (*m_menv).operator->(); }
};

/**
   \brief Apply the changes in \c lctx to \c a.
*/
expr apply_local_context(expr const & a, local_context const & lctx, optional<ro_metavar_env> const & menv);
inline expr apply_local_context(expr const & a, local_context const & lctx, ro_metavar_env const & menv) { return apply_local_context(a, lctx, some_ro_menv(menv)); }
inline expr apply_local_context(expr const & a, local_context const & lctx) { return apply_local_context(a, lctx, none_ro_menv()); }

/**
    \brief Extend the local context \c lctx with the entry <tt>lift:s:n</tt>
*/
local_context add_lift(local_context const & lctx, unsigned s, unsigned n);

/**
   \brief Add a lift:s:n operation to the context of the given metavariable.

   \pre is_metavar(m)

   \remark If menv is not none, then we use \c free_var_range to compute the free variables that may
   occur in \c m. If s > the maximum free variable that occurs in \c m, then
   we do not add a lift local entry to the local context.
*/
expr add_lift(expr const & m, unsigned s, unsigned n, optional<ro_metavar_env> const & menv);
inline expr add_lift(expr const & m, unsigned s, unsigned n) { return add_lift(m, s, n, none_ro_menv()); }
inline expr add_lift(expr const & m, unsigned s, unsigned n, ro_metavar_env const & menv) { return add_lift(m, s, n, some_ro_menv(menv)); }

/**
   \brief Extend the local context \c lctx with the entry <tt>inst:s v</tt>
*/
local_context add_inst(local_context const & lctx, unsigned s, expr const & v);

/**
   \brief Add an inst:s:v operation to the context of the given metavariable.

   \pre is_metavar(m)

   \remark If menv is not none, then we use \c free_var_range to compute the free variables that may
   occur in \c m. If s > the maximum free variable that occurs in \c m, then
   we do not add an inst local entry to the local context.
*/
expr add_inst(expr const & m, unsigned s, expr const & v, optional<ro_metavar_env> const & menv);
inline expr add_inst(expr const & m, unsigned s, expr const & v) { return add_inst(m, s, v, none_ro_menv()); }
inline expr add_inst(expr const & m, unsigned s, expr const & v, ro_metavar_env const & menv) { return add_inst(m, s, v, some_ro_menv(menv)); }

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
   \brief Return true iff \c e has a metavariable that is assigned in \c menv.
*/
bool has_assigned_metavar(expr const & e, ro_metavar_env const & menv);

/**
   \brief Return true iff \c e contains the metavariable \c m.
   The substitutions in \c menv are taken into account.

   \brief is_metavar(m)
*/
bool has_metavar(expr const & e, expr const & m, ro_metavar_env const & menv);
}
