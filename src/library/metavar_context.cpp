/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "library/replace_visitor.h"
#include "library/metavar_context.h"

namespace lean {
static name *       g_meta_prefix;
static expr *       g_dummy_type;

name mk_meta_decl_name() {
    return mk_tagged_fresh_name(*g_meta_prefix);
}

expr mk_meta_ref(name const & n) {
    return mk_metavar(n, *g_dummy_type);
}

bool is_univ_metavar_decl_ref(level const & u) {
    return is_meta(u) && is_tagged_by(meta_id(u), *g_meta_prefix);
}

bool is_metavar_decl_ref(expr const & e) {
    return is_metavar(e) && mlocal_type(e) == *g_dummy_type;
}

level metavar_context::mk_univ_metavar_decl() {
    return mk_meta_univ(mk_meta_decl_name());
}

expr metavar_context::mk_metavar_decl(local_context const & ctx, expr const & type) {
    name n = mk_meta_decl_name();
    m_decls.insert(n, metavar_decl(ctx.to_local_decls(), type));
    return mk_meta_ref(n);
}

optional<metavar_decl> metavar_context::get_metavar_decl(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto r = m_decls.find(mlocal_name(e)))
        return optional<metavar_decl>(*r);
    else
        return optional<metavar_decl>();
}

void metavar_context::assign(level const & u, level const & l) {
    lean_assert(!is_assigned(u));
    m_uassignment.insert(meta_id(u), l);
}

void metavar_context::assign(expr const & e, expr const & v) {
    lean_assert(!is_assigned(e));
    m_eassignment.insert(mlocal_name(e), v);
}

bool metavar_context::has_assigned(level const & l) const {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_univ_metavar_decl_ref(l) && is_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

bool metavar_context::has_assigned(levels const & ls) const {
    for (level const & l : ls) {
        if (has_assigned(l))
            return true;
    }
    return false;
}

bool metavar_context::has_assigned(expr const & e) const {
    if (!has_expr_metavar(e) && !has_univ_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((is_metavar_decl_ref(e) && is_assigned(e)) ||
                (is_constant(e) && has_assigned(const_levels(e))) ||
                (is_sort(e) && has_assigned(sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level metavar_context::instantiate(level const & l) {
    if (!has_assigned(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_univ_metavar_decl_ref(l)) {
                if (auto v1 = m_uassignment.find(meta_id(l))) {
                    level v2 = instantiate(*v1);
                    if (*v1 != v2) {
                        m_uassignment.insert(meta_id(l), v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

struct instantiate_fn : public replace_visitor {
    metavar_context & m_owner;

    level visit_level(level const & l) {
        return m_owner.instantiate(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) override {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) override {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) override {
        return update_mlocal(e, visit(mlocal_type(e)));
    }

    virtual expr visit_meta(expr const & m) override {
        if (is_metavar_decl_ref(m)) {
            if (auto v1 = m_owner.m_eassignment.find(mlocal_name(m))) {
                if (!has_expr_metavar(*v1)) {
                    return *v1;
                } else {
                    expr v2 = m_owner.instantiate(*v1);
                    if (v2 != *v1)
                        m_owner.m_eassignment.insert(mlocal_name(m), v2);
                    return v2;
                }
            } else {
                return m;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (is_metavar_decl_ref(f)) {
            if (auto v = m_owner.m_eassignment.find(mlocal_name(f))) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_expr_metavar(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) override {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    virtual expr visit(expr const & e) override {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_fn(metavar_context & o):m_owner(o) {}
    expr operator()(expr const & e) { return visit(e); }
};

expr metavar_context::instantiate(expr const & e) {
    return e;
}

static bool well_formed_metavar_occs(expr const & e, local_decls const & ds, metavar_context const & ctx) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e)) {
                if (auto d = ctx.get_metavar_decl(e)) {
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
    local_decls visited;
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
    return well_formed_metavar_occs(e, ctx.to_local_decls(), *this);
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
    g_meta_prefix = new name(name::mk_internal_unique_name());
    g_dummy_type  = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_metavar_context() {
    delete g_meta_prefix;
    delete g_dummy_type;
}
}
