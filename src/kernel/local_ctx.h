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
/*
inductive LocalDecl
| cdecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (bi : BinderInfo)
| ldecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (value : Expr)
*/
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
    local_decl(local_decl && other):object_ref(std::move(other)) {}
    local_decl(obj_arg o):object_ref(o) {}
    local_decl(b_obj_arg o, bool):object_ref(o, true) {}
    local_decl & operator=(local_decl const & other) { object_ref::operator=(other); return *this; }
    local_decl & operator=(local_decl && other) { object_ref::operator=(std::move(other)); return *this; }
    friend bool is_eqp(local_decl const & d1, local_decl const & d2) { return d1.raw() == d2.raw(); }
    unsigned get_idx() const { return static_cast<nat const &>(cnstr_get_ref(raw(), 0)).get_small_value(); }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 1)); }
    name const & get_user_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 2)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(raw(), 3)); }
    optional<expr> get_value() const {
        if (cnstr_tag(raw()) == 0) return none_expr();
        return some_expr(static_cast<expr const &>(cnstr_get_ref(raw(), 4)));
    }
    binder_info get_info() const;
    expr mk_ref() const;
};

/* Plain local context object used by the kernel type checker. */
class local_ctx : public object_ref {
protected:
    template<bool is_lambda> expr mk_binding(unsigned num, expr const * fvars, expr const & b, bool remove_dead_let = false) const;
public:
    local_ctx();
    explicit local_ctx(obj_arg o):object_ref(o) {}
    local_ctx(b_obj_arg o, bool):object_ref(o, true) {}
    local_ctx(local_ctx const & other):object_ref(other) {}
    local_ctx(local_ctx && other):object_ref(std::move(other)) {}
    local_ctx & operator=(local_ctx const & other) { object_ref::operator=(other); return *this; }
    local_ctx & operator=(local_ctx && other) { object_ref::operator=(std::move(other)); return *this; }

    bool empty() const;

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

    /** \brief Return the local declarations for the given reference. */
    optional<local_decl> find_local_decl(name const & n) const;
    optional<local_decl> find_local_decl(expr const & e) const { return find_local_decl(fvar_name(e)); }

    local_decl get_local_decl(name const & n) const;
    local_decl get_local_decl(expr const & e) const { return get_local_decl(fvar_name(e)); }

    /* \brief Return type of the given free variable.
       \pre is_fvar(e) */
    expr get_type(expr const & e) const { return get_local_decl(e).get_type(); }

    /** Return the free variable associated with the given name.
        \pre get_local_decl(n) */
    expr get_local(name const & n) const;

    /** \brief Remove the given local decl. */
    void clear(local_decl const & d);

    expr mk_lambda(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let = false) const;
    expr mk_pi(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let = false) const;
    expr mk_lambda(buffer<expr> const & fvars, expr const & e, bool remove_dead_let = false) const { return mk_lambda(fvars.size(), fvars.data(), e, remove_dead_let); }
    expr mk_pi(buffer<expr> const & fvars, expr const & e, bool remove_dead_let = false) const { return mk_pi(fvars.size(), fvars.data(), e, remove_dead_let); }
    expr mk_lambda(expr const & fvar, expr const & e) { return mk_lambda(1, &fvar, e); }
    expr mk_pi(expr const & fvar, expr const & e) { return mk_pi(1, &fvar, e); }
    expr mk_lambda(std::initializer_list<expr> const & fvars, expr const & e) { return mk_lambda(fvars.size(), fvars.begin(), e); }
    expr mk_pi(std::initializer_list<expr> const & fvars, expr const & e) { return mk_pi(fvars.size(), fvars.begin(), e); }
};

void initialize_local_ctx();
void finalize_local_ctx();
}
