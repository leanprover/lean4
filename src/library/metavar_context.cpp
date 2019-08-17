/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/metavar_util.h"
#include "library/metavar_context.h"

namespace lean {
static name *       g_meta_prefix;
static expr *       g_dummy_type;

metavar_decl::metavar_decl(name const & user_name, local_context const & lctx, expr const & type):
    object_ref(mk_cnstr(0, user_name, lctx, type)) {
}

metavar_decl::metavar_decl():
    metavar_decl(name(), local_context(), expr()) {}

static expr mk_meta_ref(name const & n) {
    return mk_metavar(n, *g_dummy_type);
}

bool is_metavar_decl_ref(level const & u) {
    return is_mvar(u) && is_prefix_of(*g_meta_prefix, mvar_id(u));
}

bool is_metavar_decl_ref(expr const & e) {
    return is_mvar(e) && mvar_type(e) == *g_dummy_type;
}

name get_metavar_decl_ref_suffix(level const & u) {
    lean_assert(is_metavar_decl_ref(u));
    return mvar_id(u).replace_prefix(*g_meta_prefix, name());
}

name get_metavar_decl_ref_suffix(expr const & e) {
    lean_assert(is_metavar_decl_ref(e));
    return mvar_name(e).replace_prefix(*g_meta_prefix, name());
}

metavar_context::delayed_assignment::delayed_assignment(local_context const & lctx, exprs const & locals, expr const & v):
    object_ref(mk_cnstr(0, lctx, locals, v)) {
}

metavar_context::delayed_assignment::delayed_assignment():
    delayed_assignment(local_context(), exprs(), expr()) {
}

// TODO(Leo): fix this
static name mk_meta_decl_name() {
    return mk_tagged_fresh_name(*g_meta_prefix);
}

extern "C" object* lean_mk_metavar_ctx(object*);
extern "C" object* lean_metavar_ctx_mk_decl(object*, object*, object*, object*, object*);
extern "C" object* lean_metavar_ctx_find_decl(object*, object*);
extern "C" object* lean_metavar_ctx_assign_level(object*, object*, object*);
extern "C" object* lean_metavar_ctx_assign_expr(object*, object*, object*);
extern "C" object* lean_metavar_ctx_assign_delayed(object*, object*, object*, object*, object*);
extern "C" object* lean_metavar_ctx_get_level_assignment(object*, object*);
extern "C" object* lean_metavar_ctx_get_expr_assignment(object*, object*);
extern "C" object* lean_metavar_ctx_get_delayed_assignment(object*, object*);
extern "C" uint8 lean_metavar_ctx_is_level_assigned(object*, object*);
extern "C" uint8 lean_metavar_ctx_is_expr_assigned(object*, object*);
extern "C" uint8 lean_metavar_ctx_is_delayed_assigned(object*, object*);
extern "C" object* lean_metavar_ctx_erase_delayed(object*, object*);

metavar_context::metavar_context():
    object_ref(lean_mk_metavar_ctx(box(0))) {
}

bool metavar_context::is_assigned(level const & l) const {
    lean_assert(is_metavar_decl_ref(l));
    return lean_metavar_ctx_is_level_assigned(to_obj_arg(), mvar_id(l).to_obj_arg());
}

bool metavar_context::is_assigned(expr const & m) const {
    lean_assert(is_metavar_decl_ref(m));
    return lean_metavar_ctx_is_expr_assigned(to_obj_arg(), mvar_name(m).to_obj_arg());
}

bool metavar_context::is_delayed_assigned(expr const & m) const {
    lean_assert(is_metavar_decl_ref(m));
    return lean_metavar_ctx_is_delayed_assigned(to_obj_arg(), mvar_name(m).to_obj_arg());
}

level metavar_context::mk_univ_metavar_decl() {
    // TODO(Leo): should use name_generator
    return mk_univ_mvar(mk_meta_decl_name());
}

expr metavar_context::mk_metavar_decl(name const & user_name, local_context const & lctx, expr const & type) {
    // TODO(Leo): should use name_generator
    name n = mk_meta_decl_name();
    m_obj = lean_metavar_ctx_mk_decl(m_obj, n.to_obj_arg(), user_name.to_obj_arg(), lctx.to_obj_arg(), head_beta_reduce(type).to_obj_arg());
    lean_assert(find_metavar_decl(mk_meta_ref(n)));
    return mk_meta_ref(n);
}

optional<metavar_decl> metavar_context::find_metavar_decl(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    return to_optional<metavar_decl>(lean_metavar_ctx_find_decl(to_obj_arg(), mvar_name(e).to_obj_arg()));
}

metavar_decl metavar_context::get_metavar_decl(expr const & e) const {
    if (auto r = find_metavar_decl(e))
        return *r;
    else
        throw exception("unknown metavariable");
}

optional<local_decl> metavar_context::find_local_decl(expr const & mvar, name const & n) const {
    auto mdecl = find_metavar_decl(mvar);
    if (!mdecl) return optional<local_decl>();
    return mdecl->get_context().find_local_decl(n);
}

local_decl metavar_context::get_local_decl(expr const & mvar, name const & n) const {
    return get_metavar_decl(mvar).get_context().get_local_decl(n);
}

expr metavar_context::get_local(expr const & mvar, name const & n) const {
    return get_local_decl(mvar, n).mk_ref();
}

void metavar_context::assign(level const & u, level const & l) {
    m_obj = lean_metavar_ctx_assign_level(m_obj, mvar_id(u).to_obj_arg(), l.to_obj_arg());
    lean_assert(is_assigned(u));
}

void metavar_context::assign(expr const & e, expr const & v) {
    lean_assert(!is_delayed_assigned(e));
    m_obj = lean_metavar_ctx_assign_expr(m_obj, mvar_name(e).to_obj_arg(), v.to_obj_arg());
    lean_assert(is_assigned(e));
}

void metavar_context::assign(expr const & e, local_context const & lctx, exprs const & locals, expr const & v) {
    m_obj = lean_metavar_ctx_assign_delayed(m_obj, mvar_name(e).to_obj_arg(), lctx.to_obj_arg(), locals.to_obj_arg(), v.to_obj_arg());
    lean_assert(is_delayed_assigned(e));
}

optional<level> metavar_context::get_assignment(level const & l) const {
    lean_assert(is_metavar_decl_ref(l));
    return to_optional<level>(lean_metavar_ctx_get_level_assignment(to_obj_arg(), mvar_id(l).to_obj_arg()));
}

optional<expr> metavar_context::get_assignment(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    return to_optional<expr>(lean_metavar_ctx_get_expr_assignment(to_obj_arg(), mvar_name(e).to_obj_arg()));
}

optional<metavar_context::delayed_assignment> metavar_context::get_delayed_assignment(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    return to_optional<metavar_context::delayed_assignment>(lean_metavar_ctx_get_delayed_assignment(to_obj_arg(), mvar_name(e).to_obj_arg()));
}

struct metavar_context::interface_impl {
    metavar_context & m_ctx;
    /* We store the set of delayed assigned variables that have been found to prevent their values
       from being visited over and over again. */
    name_set          m_delayed_found;
    interface_impl(metavar_context const & ctx):m_ctx(const_cast<metavar_context&>(ctx)) {}

    static bool is_mvar(level const & l) { return is_metavar_decl_ref(l); }
    bool is_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    optional<level> get_assignment(level const & l) const { return m_ctx.get_assignment(l); }
    void assign(level const & u, level const & v) { m_ctx.assign(u, v); }

    static bool is_mvar(expr const & e) { return is_metavar_decl_ref(e); }

    optional<expr> check_delayed_assignment(expr const & e) {
        lean_assert(is_metavar_decl_ref(e));
        optional<delayed_assignment> d = m_ctx.get_delayed_assignment(e);
        if (!d)
            return none_expr();
        if (m_delayed_found.contains(mvar_name(e)))
            return none_expr();
        /* Remark: a delayed assignment can be transformed in a regular assignment
           as soon as all metavariables occurring in the assigned value have
           been assigned. */
        expr new_v = m_ctx.instantiate_mvars(d->get_val());
        if (has_expr_metavar(new_v)) {
            m_delayed_found.insert(mvar_name(e));
            if (!is_eqp(new_v, d->get_val()))
                m_ctx.assign(e, d->get_lctx(), d->get_locals(), new_v);
            return none_expr();
        } else {
            m_ctx.m_obj = lean_metavar_ctx_erase_delayed(m_ctx.m_obj, mvar_name(e).to_obj_arg());
            lean_assert(!m_ctx.is_delayed_assigned(e));
            buffer<expr> locals;
            to_buffer(d->get_locals(), locals);
            new_v = abstract(new_v, locals.size(), locals.data());
            unsigned i = locals.size();
            while (i > 0) {
                --i;
                local_decl decl = d->get_lctx().get_local_decl(locals[i]);
                expr type       = abstract(decl.get_type(), i, locals.data());
                if (optional<expr> letval = decl.get_value()) {
                    letval = abstract(*letval, i, locals.data());
                    new_v  = mk_let(decl.get_user_name(), type, *letval, new_v);
                } else {
                    new_v  = mk_lambda(decl.get_user_name(), type, new_v, decl.get_info());
                }
            }
            m_ctx.assign(e, new_v);
            return some_expr(new_v);
        }
    }

    bool is_assigned(expr const & e) const {
        lean_assert(is_metavar_decl_ref(e));
        return m_ctx.is_assigned(e) || const_cast<metavar_context::interface_impl*>(this)->check_delayed_assignment(e);
    }

    optional<expr> get_assignment(expr const & e) const {
        if (optional<expr> v = m_ctx.get_assignment(e))
            return v;
        if (optional<expr> v = const_cast<metavar_context::interface_impl*>(this)->check_delayed_assignment(e))
            return v;
        return none_expr();
    }

    void assign(expr const & m, expr const & v) { m_ctx.assign(m, v); }
    bool in_tmp_mode() const { return false; }
};


bool metavar_context::has_assigned(level const & l) const {
    return ::lean::has_assigned(interface_impl(*this), l);
}

bool metavar_context::has_assigned(expr const & e) const {
    return ::lean::has_assigned(interface_impl(*this), e);
}

level metavar_context::instantiate_mvars(level const & l) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, l);
}

expr metavar_context::instantiate_mvars(expr const & e) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, e);
}

void metavar_context::instantiate_mvars_at_type_of(expr const & m) {
    metavar_decl d = get_metavar_decl(m);
    expr type      = d.get_type();
    expr new_type  = instantiate_mvars(type);
    if (new_type != type) {
        m_obj = lean_metavar_ctx_mk_decl(m_obj,
                                         mvar_name(m).to_obj_arg(),
                                         d.get_user_name().to_obj_arg(),
                                         d.get_context().to_obj_arg(),
                                         new_type.to_obj_arg());
    }
}

template<typename C>
static bool well_formed_metavar_occs(expr const & e, C const & ds, metavar_context const & ctx) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e)) {
                if (auto d = ctx.find_metavar_decl(e)) {
                    if (!d->get_context().is_subset_of(ds)) {
                        /* invalid metavariable context */
                        ok = false;
                        return false;
                    }
                } else {
                    /* undefined metavariable */
                    ok = false;
                    return false;
                }
            }
            return true;
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx) const {
    bool ok = true;
    name_set visited;
    ctx.for_each([&](local_decl const & d) {
            if (!well_formed_metavar_occs(d.get_type(), visited, *this)) {
                ok = false;
                lean_unreachable();
            }
            if (auto v = d.get_value()) {
                if (!well_formed_metavar_occs(*v, visited, *this)) {
                    ok = false;
                    lean_unreachable();
                }
            }
            visited.insert(d.get_name());
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx, expr const & e) const {
    return well_formed_metavar_occs(e, ctx, *this);
}

bool well_formed(local_context const & lctx, metavar_context const & mctx) {
    if (!lctx.well_formed()) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx)) {
        lean_unreachable();
        return false;
    }
    return true;
}

bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e) {
    if (!lctx.well_formed(e)) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx, e)) {
        lean_unreachable();
        return false;
    }
    return true;
}

void initialize_metavar_context() {
    g_meta_prefix = new name("_mlocal");
    register_name_generator_prefix(*g_meta_prefix);
    g_dummy_type  = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_metavar_context() {
    delete g_meta_prefix;
    delete g_dummy_type;
}
}
