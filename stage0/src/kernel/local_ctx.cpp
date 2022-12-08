/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "runtime/sstream.h"
#include "kernel/local_ctx.h"
#include "kernel/abstract.h"

namespace lean {
static expr *       g_dummy_type;
static local_decl * g_dummy_decl;

extern "C" object * lean_mk_local_decl(object * index, object * fvarid, object * user_name, object * type, uint8 bi);
extern "C" object * lean_mk_let_decl(object * index, object * fvarid, object * user_name, object * type, object * val);
extern "C" uint8 lean_local_decl_binder_info(object * d);

local_decl::local_decl():object_ref(*g_dummy_decl) {}

local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, expr const & v):
    object_ref(lean_mk_let_decl(nat(idx).to_obj_arg(), n.to_obj_arg(), un.to_obj_arg(), t.to_obj_arg(), v.to_obj_arg())) {
}

local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, binder_info bi):
    object_ref(lean_mk_local_decl(nat(idx).to_obj_arg(), n.to_obj_arg(), un.to_obj_arg(), t.to_obj_arg(), static_cast<uint8>(bi))) {
}

local_decl::local_decl(local_decl const & d, expr const & t, expr const & v):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, v) {}

local_decl::local_decl(local_decl const & d, expr const & t):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, d.get_info()) {}

binder_info local_decl::get_info() const {
    return static_cast<binder_info>(lean_local_decl_binder_info(to_obj_arg()));
}

expr local_decl::mk_ref() const {
    return mk_fvar(get_name());
}

extern "C" object * lean_mk_empty_local_ctx(object*);
extern "C" object * lean_local_ctx_num_indices(object*);
extern "C" uint8 lean_local_ctx_is_empty(object*);
extern "C" object * lean_local_ctx_mk_local_decl(object * lctx, object * name, object * user_name, object * expr, uint8 bi);
extern "C" object * lean_local_ctx_mk_let_decl(object * lctx, object * name, object * user_name, object * type, object * value, uint8 non_dep);
extern "C" object * lean_local_ctx_find(object * lctx, object * name);
extern "C" object * lean_local_ctx_erase(object * lctx, object * name);

local_ctx::local_ctx():object_ref(lean_mk_empty_local_ctx(box(0))) {
}

bool local_ctx::empty() const {
    return lean_local_ctx_is_empty(to_obj_arg());
}

local_decl local_ctx::mk_local_decl(name const & n, name const & un, expr const & type, expr const & value) {
    unsigned idx = unbox(lean_local_ctx_num_indices(to_obj_arg()));
    m_obj = lean_local_ctx_mk_let_decl(raw(), n.to_obj_arg(), un.to_obj_arg(), type.to_obj_arg(), value.to_obj_arg(), false);
    return local_decl(idx, n, un, type, value);
}

local_decl local_ctx::mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi) {
    unsigned idx = unbox(lean_local_ctx_num_indices(to_obj_arg()));
    m_obj = lean_local_ctx_mk_local_decl(raw(), n.to_obj_arg(), un.to_obj_arg(), type.to_obj_arg(), static_cast<uint8>(bi));
    return local_decl(idx, n, un, type, bi);
}

optional<local_decl> local_ctx::find_local_decl(name const & n) const {
    return to_optional<local_decl>(lean_local_ctx_find(to_obj_arg(), n.to_obj_arg()));
}

local_decl local_ctx::get_local_decl(name const & n) const {
    if (optional<local_decl> r = find_local_decl(n)) {
        return *r;
    } else {
        // lean_assert(false);
        throw exception(sstream() << "unknown free variable: " << n);
    }
}

expr local_ctx::get_local(name const & n) const {
    lean_assert(find_local_decl(n));
    return get_local_decl(n).mk_ref();
}

void local_ctx::clear(local_decl const & d) {
    m_obj = lean_local_ctx_erase(m_obj, d.get_name().to_obj_arg());
}

template<bool is_lambda>
expr local_ctx::mk_binding(unsigned num, expr const * fvars, expr const & b, bool remove_dead_let) const {
    expr r     = abstract(b, num, fvars);
    unsigned i = num;
    while (i > 0) {
        --i;
        local_decl const & decl = get_local_decl(fvar_name(fvars[i]));
        if (optional<expr> const & opt_val = decl.get_value()) {
            if (!remove_dead_let || has_loose_bvar(r, 0)) {
                expr type  = abstract(decl.get_type(), i, fvars);
                expr value = abstract(*opt_val, i, fvars);
                r = ::lean::mk_let(decl.get_user_name(), type, value, r);
            } else {
                r = lower_loose_bvars(r, 1, 1);
            }
        } else if (is_lambda) {
            expr type = abstract(decl.get_type(), i, fvars);
            r = ::lean::mk_lambda(decl.get_user_name(), type, r, decl.get_info());
        } else {
            expr type = abstract(decl.get_type(), i, fvars);
            r = ::lean::mk_pi(decl.get_user_name(), type, r, decl.get_info());
        }
    }
    return r;
}

expr local_ctx::mk_lambda(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let) const {
    return mk_binding<true>(num, fvars, e, remove_dead_let);
}

expr local_ctx::mk_pi(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let) const {
    return mk_binding<false>(num, fvars, e, remove_dead_let);
}

void initialize_local_ctx() {
    g_dummy_type   = new expr(mk_constant(name::mk_internal_unique_name()));
    mark_persistent(g_dummy_type->raw());
    g_dummy_decl   = new local_decl(std::numeric_limits<unsigned>::max(),
                                    name("__local_decl_for_default_constructor"), name("__local_decl_for_default_constructor"),
                                    mk_Prop(), mk_binder_info());
    mark_persistent(g_dummy_decl->raw());
}

void finalize_local_ctx() {
    delete g_dummy_decl;
    delete g_dummy_type;
}
}
