/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_generator.h"
#include "util/rb_map.h"
#include "util/name_map.h"
#include "kernel/expr.h"

namespace lean {
/* TODO(Leo): implement using runtime objects */
class local_decl {
public:
    struct cell {
        /* <name> : <type> := <value>
           m_user_name is used for interacting with the user, and it may not be not unique. */
        name               m_name; /* this one is unique */
        name               m_user_name;
        expr               m_type;
        optional<expr>     m_value;
        binder_info        m_bi;
        unsigned           m_idx;
        MK_LEAN_RC(); // Declare m_rc counter
        void dealloc();
        cell(unsigned idx, name const & n, name const & un, expr const & t, optional<expr> const & v,
             binder_info const & bi);
    };
private:
    cell * m_ptr;
    friend class local_ctx;
    friend class local_context;
    friend void initialize_local_ctx();
    local_decl(unsigned idx, name const & n, name const & un, expr const & t, optional<expr> const & v, binder_info const & bi);
    local_decl(local_decl const & d, expr const & t, optional<expr> const & v);
public:
    local_decl();
    local_decl(local_decl const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    local_decl(local_decl && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~local_decl() { if (m_ptr) m_ptr->dec_ref(); }
    local_decl & operator=(local_decl const & s) { LEAN_COPY_REF(s); }
    local_decl & operator=(local_decl && s) { LEAN_MOVE_REF(s); }

    friend bool is_eqp(local_decl const & a, local_decl const & b) { return a.m_ptr == b.m_ptr; }

    name const & get_name() const { return m_ptr->m_name; }
    name const & get_user_name() const { return m_ptr->m_user_name; }
    expr const & get_type() const { return m_ptr->m_type; }
    optional<expr> const & get_value() const { return m_ptr->m_value; }
    binder_info const & get_info() const { return m_ptr->m_bi; }
    expr mk_ref() const;
    unsigned get_idx() const { return m_ptr->m_idx; }
};

/* Plain local context object used by the kernel type checker. */
class local_ctx {
protected:
    typedef unsigned_map<local_decl> idx2local_decl;
    unsigned                  m_next_idx;
    idx2local_decl            m_idx2local_decl;
    name_map<local_decl>      m_name2local_decl; // mapping from unique identifier to local_decl

    template<bool is_lambda> expr mk_binding(unsigned num, expr const * fvars, expr const & b) const;

    local_decl mk_local_decl(name const & n, name const & un, expr const & type,
                             optional<expr> const & value, binder_info const & bi);
public:
    local_ctx():m_next_idx(0) {}

    bool empty() const { return m_idx2local_decl.empty(); }

    expr mk_local_decl(name const & n, expr const & type, binder_info const & bi = binder_info()) {
        return mk_local_decl(n, n, type, none_expr(), bi).mk_ref();
    }

    expr mk_local_decl(name const & n, expr const & type, expr const & value) {
        return mk_local_decl(n, n, type, some_expr(value), binder_info()).mk_ref();
    }

    expr mk_local_decl(name const & n, name const & un, expr const & type, binder_info const & bi = binder_info()) {
        return mk_local_decl(n, un, type, none_expr(), bi).mk_ref();
    }

    expr mk_local_decl(name const & n, name const & un, expr const & type, expr const & value) {
        return mk_local_decl(n, un, type, some_expr(value), binder_info()).mk_ref();
    }

    /** \brief Return the local declarations for the given reference.

        \pre is_fvar(e) */
    optional<local_decl> find_local_decl(expr const & e) const;
    optional<local_decl> find_local_decl(name const & n) const;

    local_decl const & get_local_decl(name const & n) const;
    local_decl const & get_local_decl(expr const & e) const { return get_local_decl(mlocal_name(e)); }

    /** \brief Traverse local declarations based on the order they were created */
    void for_each(std::function<void(local_decl const &)> const & fn) const;
    optional<local_decl> find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT
    optional<local_decl> back_find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT

    /** Return the free variable associated with the given name.
        \pre get_local_decl(n) */
    expr get_local(name const & n) const;

    /** \brief Remove the given local decl. */
    void clear(local_decl const & d);

    expr mk_lambda(unsigned num, expr const * fvars, expr const & e) const;
    expr mk_pi(unsigned num, expr const * fvars, expr const & e) const;
    expr mk_lambda(buffer<expr> const & fvars, expr const & e) const { return mk_lambda(fvars.size(), fvars.data(), e); }
    expr mk_pi(buffer<expr> const & fvars, expr const & e) const { return mk_pi(fvars.size(), fvars.data(), e); }
    expr mk_lambda(expr const & fvar, expr const & e) { return mk_lambda(1, &fvar, e); }
    expr mk_pi(expr const & fvar, expr const & e) { return mk_pi(1, &fvar, e); }
    expr mk_lambda(std::initializer_list<expr> const & fvars, expr const & e) { return mk_lambda(fvars.size(), fvars.begin(), e); }
    expr mk_pi(std::initializer_list<expr> const & fvars, expr const & e) { return mk_pi(fvars.size(), fvars.begin(), e); }

    friend bool is_decl_eqp(local_ctx const & ctx1, local_ctx const & ctx2) {
        return is_eqp(ctx1.m_name2local_decl, ctx2.m_name2local_decl);
    }

    friend bool equal_locals(local_ctx const & ctx1, local_ctx const & ctx2) {
        return is_decl_eqp(ctx1, ctx2) || ctx1.m_name2local_decl.equal_keys(ctx2.m_name2local_decl);
    }
};

void initialize_local_ctx();
void finalize_local_ctx();
}
