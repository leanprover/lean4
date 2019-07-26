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
class local_decl : public object_ref {
    friend class local_ctx;
    friend class local_context;
    friend void initialize_local_ctx();
    local_decl(unsigned idx, name const & n, name const & un, expr const & t, expr const & v);
    local_decl(local_decl const & d, expr const & t, expr const & v);
    local_decl(unsigned idx, name const & n, name const & un, expr const & t, binder_info bi);
    local_decl(local_decl const & d, expr const & t);
public:
    local_decl();
    local_decl(local_decl const & other):object_ref(other) {}
    local_decl(local_decl && other):object_ref(other) {}
    local_decl & operator=(local_decl const & other) { object_ref::operator=(other); return *this; }
    local_decl & operator=(local_decl && other) { object_ref::operator=(other); return *this; }
    friend bool is_eqp(local_decl const & d1, local_decl const & d2) { return d1.raw() == d2.raw(); }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 0)); }
    name const & get_user_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 1)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(raw(), 2)); }
    optional<expr> get_value() const {
        /* Remark: if we decide to expose `local_decl` in Lean, we will need to use Lean `option` type. */
        if (is_scalar(cnstr_get(raw(), 3))) return none_expr();
        else return some_expr(static_cast<expr const &>(cnstr_get_ref(raw(), 3)));
    }
    unsigned get_idx() const { return cnstr_get_scalar<unsigned>(raw(), sizeof(object*)*4); }
    binder_info get_info() const { return static_cast<binder_info>(cnstr_get_scalar<unsigned char>(raw(), sizeof(object*)*4+sizeof(unsigned))); }
    expr mk_ref() const;
};

/* Plain local context object used by the kernel type checker. */
class local_ctx {
protected:
    unsigned                  m_next_idx;
    name_map<local_decl>      m_name2local_decl; // mapping from unique identifier to local_decl

    template<bool is_lambda> expr mk_binding(unsigned num, expr const * fvars, expr const & b) const;
public:
    local_ctx():m_next_idx(0) {}

    bool empty() const { return m_name2local_decl.empty(); }

    /* Low level `mk_local_decl` */
    local_decl mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi);
    /* Low level `mk_local_decl` */
    local_decl mk_local_decl(name const & n, name const & un, expr const & type, expr const & value);

    expr mk_local_decl(name_generator & g, name const & un, expr const & type, binder_info bi = mk_binder_info()) {
        return mk_local_decl(g.next(), un, type, bi).mk_ref();
    }

    expr mk_local_decl(name_generator & g, name const & un, expr const & type, expr const & value) {
        return mk_local_decl(g.next(), un, type, value).mk_ref();
    }

    /** \brief Return the local declarations for the given reference.

        \pre is_fvar(e) */
    optional<local_decl> find_local_decl(expr const & e) const;
    optional<local_decl> find_local_decl(name const & n) const;

    local_decl const & get_local_decl(name const & n) const;
    local_decl const & get_local_decl(expr const & e) const { return get_local_decl(fvar_name(e)); }

    /* \brief Return type of the given free variable.
       \pre is_fvar(e) */
    expr get_type(expr const & e) const { return get_local_decl(e).get_type(); }

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
