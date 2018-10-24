/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "util/fresh_name.h"
#include "util/list_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "library/pp_options.h"
#include "library/local_context.h"
#include "library/metavar_context.h"
#include "library/trace.h"

namespace lean {
name mk_local_decl_name() {
    return mk_fresh_name();
}

struct depends_on_fn {
    metavar_context const & m_mctx;
    local_context const *   m_lctx;
    unsigned                m_num;
    expr const *            m_locals;
    name_set                m_visited_mvars;
    name_set                m_visited_decls;

    depends_on_fn(metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals):
        m_mctx(mctx), m_lctx(&lctx), m_num(num), m_locals(locals) {
        lean_assert(std::all_of(locals, locals+num, is_local_decl_ref));
    }

    depends_on_fn(metavar_context const & mctx, unsigned num, expr const * locals):
        m_mctx(mctx), m_lctx(nullptr), m_num(num), m_locals(locals) {
        lean_assert(std::all_of(locals, locals+num, is_local_decl_ref));
    }

    bool visit_local(expr const & e) {
        lean_assert(is_local_decl_ref(e));
        if (std::any_of(m_locals, m_locals + m_num,
                        [&](expr const & l) { return local_name(e) == local_name(l); }))
            return true;

        if (!m_lctx || m_visited_decls.contains(local_name(e)))
            return false;
        m_visited_decls.insert(local_name(e));
        optional<local_decl> decl = m_lctx->find_local_decl(e);
        if (!decl)
            return false;
        if (visit(decl->get_type()))
            return true;
        if (optional<expr> v = decl->get_value())
            return visit(*v);
        else
            return false;
    }

    bool visit_metavar(expr const & e) {
        lean_assert(is_metavar_decl_ref(e));
        if (m_visited_mvars.contains(mvar_name(e)))
            return false;
        m_visited_mvars.insert(mvar_name(e));
        optional<metavar_decl> decl = m_mctx.find_metavar_decl(e);
        if (!decl)
            return false;
        if (visit(decl->get_type()))
            return true;
        if (auto v = m_mctx.get_assignment(e)) {
            if (visit(*v))
                return true;
        }
        return false;
    }

    bool visit(expr const & e) {
        if (!has_local(e) && !has_expr_metavar(e))
            return false;
        bool found = false;
        for_each(e, [&](expr const & e, unsigned) {
                if (found) return false;
                if (!has_local(e) && !has_expr_metavar(e)) return false;
                if (is_local_decl_ref(e) && visit_local(e)) {
                    found = true;
                    return false;
                }
                if (is_metavar_decl_ref(e) && visit_metavar(e)) {
                    found = true;
                    return false;
                }
                return true;
            });
        return found;
    }

    bool operator()(expr const & e) { return visit(e); }
};

bool depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals) {
    return depends_on_fn(mctx, num, locals)(e);
}

bool depends_on(local_decl const & d, metavar_context const & mctx, unsigned num, expr const * locals) {
    depends_on_fn fn(mctx, num, locals);
    if (fn(d.get_type()))
        return true;
    if (auto v = d.get_value()) {
        return fn(*v);
    }
    return false;
}

bool depends_on(expr const & e, metavar_context const & mctx, buffer<expr> const & locals) {
    return depends_on_fn(mctx, locals.size(), locals.data())(e);
}

bool depends_on(local_decl const & d, metavar_context const & mctx, buffer<expr> const & locals) {
    return depends_on(d, mctx, locals.size(), locals.data());
}

bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals) {
    return depends_on_fn(mctx, lctx, num, locals)(e);
}

expr local_context::mk_local_decl(name const & n, name const & un, expr const & type, optional<expr> const & value, binder_info bi) {
    local_decl d = value ? local_ctx::mk_local_decl(n, un, type, *value) : local_ctx::mk_local_decl(n, un, type, bi);
    m_idx2local_decl.insert(d.get_idx(), d);
    return d.mk_ref();
}

expr local_context::mk_local_decl(expr const & type, binder_info bi) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, none_expr(), bi);
}

expr local_context::mk_local_decl(expr const & type, expr const & value) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, some_expr(value), mk_binder_info());
}

expr local_context::mk_local_decl(name const & un, expr const & type, binder_info bi) {
    return mk_local_decl(mk_local_decl_name(), un, type, none_expr(), bi);
}

expr local_context::mk_local_decl(name const & un, expr const & type, expr const & value) {
    return mk_local_decl(mk_local_decl_name(), un, type, some_expr(value), mk_binder_info());
}

expr local_context::mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi) {
    return mk_local_decl(n, un, type, none_expr(), bi);
}

expr local_context::mk_local_decl(name const & n, name const & un, expr const & type, expr const & value) {
    return mk_local_decl(n, un, type, some_expr(value), mk_binder_info());
}

optional<local_decl> local_context::back_find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.back_find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

void local_context::clear(local_decl const & d) {
    lean_assert(find_local_decl(d.get_name()));
    local_ctx::clear(d);
    m_idx2local_decl.erase(d.get_idx());
}

optional<local_decl> local_context::find_local_decl_from_user_name(name const & n) const {
    return back_find_if([&](local_decl const & d) { return d.get_user_name() == n; });
}

optional<local_decl> local_context::find_last_local_decl() const {
    if (m_idx2local_decl.empty()) return optional<local_decl>();
    return optional<local_decl>(m_idx2local_decl.max());
}

local_decl local_context::get_last_local_decl() const {
    if (m_idx2local_decl.empty()) throw("unknown local constant, context is empty");
    return m_idx2local_decl.max();
}

void local_context::for_each(std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) { fn(d); });
}

optional<local_decl> local_context::find_if(std::function<bool(local_decl const &)> const & pred) const {
    return m_idx2local_decl.find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

void local_context::for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each_greater(d.get_idx(), [&](unsigned, local_decl const & d) { return fn(d); });
}

void local_context::pop_local_decl() {
    lean_assert(!m_idx2local_decl.empty());
    local_decl d = m_idx2local_decl.max();
    m_name2local_decl.erase(d.get_name());
    m_idx2local_decl.erase(d.get_idx());
}

bool local_context::rename_user_name(name const & from, name const & to) {
    if (auto d = find_local_decl_from_user_name(from)) {
        local_decl new_d;
        if (d->get_value())
            new_d = local_decl(d->get_idx(), d->get_name(), to, d->get_type(), *d->get_value());
        else
            new_d = local_decl(d->get_idx(), d->get_name(), to, d->get_type(), d->get_info());
        m_idx2local_decl.insert(d->get_idx(), new_d);
        m_name2local_decl.insert(d->get_name(), new_d);
        return true;
    } else {
        return false;
    }
}

optional<local_decl> local_context::has_dependencies(local_decl const & d, metavar_context const & mctx) const {
    lean_assert(find_local_decl(d.get_name()));
    expr l = d.mk_ref();
    optional<local_decl> r;
    for_each_after(d, [&](local_decl const & d2) {
            if (r) return;
            if (depends_on(d2, mctx, 1, &l))
                r = d2;
        });
    return r;
}

bool local_context::is_subset_of(name_set const & ls) const {
    // TODO(Leo): we can improve performance by implementing the subset operation in the rb_map/rb_tree class
    return !static_cast<bool>(m_name2local_decl.find_if([&](name const & n, local_decl const &) {
                return !ls.contains(n);
            }));
}

bool local_context::is_subset_of(local_context const & ctx) const {
    // TODO(Leo): we can improve performance by implementing the subset operation in the rb_map/rb_tree class
    return !static_cast<bool>(m_name2local_decl.find_if([&](name const & n, local_decl const &) {
                return !ctx.m_name2local_decl.contains(n);
            }));
}

local_context local_context::remove(buffer<expr> const & locals) const {
    lean_assert(std::all_of(locals.begin(), locals.end(),
                            [&](expr const & l) {
                                return is_local_decl_ref(l) && find_local_decl(l);
                            }));
    /* TODO(Leo): check whether the following loop is a performance bottleneck. */
    local_context r          = *this;
    for (expr const & l : locals) {
        local_decl d = get_local_decl(l);
        r.m_name2local_decl.erase(local_name(l));
        r.m_idx2local_decl.erase(d.get_idx());
    }
    lean_assert(r.well_formed());
    return r;
}

/* Return true iff all local_decl references in \c e are in \c s. */
static bool locals_subset_of(expr const & e, name_set const & s) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false; // stop search
            if (is_local_decl_ref(e) && !s.contains(local_name(e))) {
                ok = false;
                return false;
            }
            return true;
        });
    return ok;
}

bool local_context::well_formed() const {
    bool ok = true;
    name_set found_locals;
    for_each([&](local_decl const & d) {
            if (!locals_subset_of(d.get_type(), found_locals)) {
                ok = false;
                lean_unreachable();
            }
            if (auto v = d.get_value()) {
                if (!locals_subset_of(*v, found_locals)) {
                    ok = false;
                    lean_unreachable();
                }
            }
            found_locals.insert(d.get_name());
        });
    return ok;
}

bool local_context::well_formed(expr const & e) const {
    bool ok = true;
    ::lean::for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (is_local_decl_ref(e) && !find_local_decl(e)) {
                ok = false;
            }
            return true;
        });
    return ok;
}

format local_context::pp(formatter const & fmt, std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    options const & opts = fmt.get_options();
    unsigned indent      = get_pp_indent(opts);
    unsigned max_hs      = get_pp_goal_max_hyps(opts);
    bool first           = true;
    unsigned i           = 0;
    format ids;
    optional<expr> type;
    format r;
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            if (!pred(d))
                return;
            if (i >= max_hs)
                return;
            i++;
            if (type && (d.get_type() != *type || d.get_value())) {
                // add (ids : type) IF the d.get_type() != type OR d is a let-decl
                if (first) first = false;
                else r += comma() + line();

                r += group(ids + space() + colon() + nest(indent, line() + fmt(*type)));
                type = optional<expr>();
                ids  = format();
            }

            name n = sanitize_if_fresh(d.get_user_name());
            n = sanitize_name_generator_name(n);

            if (d.get_value()) {
                if (first) first = false;
                else r += comma() + line();
                r += group(format(n) + space() + colon() + space() + fmt(d.get_type()) +
                           space() + format(":=") + nest(indent, line() + fmt(*d.get_value())));
            } else if (!type) {
                lean_assert(!d.get_value());
                ids  = format(n);
                type = d.get_type();
            } else {
                lean_assert(!d.get_value());
                lean_assert(type && d.get_type() == *type);
                ids += space() + format(n);
            }
        });
    if (type) {
        if (!first) r += comma() + line();
        r += group(ids + space() + colon() + nest(indent, line() + fmt(*type)));
    }
    if (get_pp_goal_compact(opts))
        r = group(r);
    return r;
}

bool local_context::uses_user_name(name const & n) const {
    return static_cast<bool>(m_idx2local_decl.find_if([&](unsigned, local_decl const & d) {
                return d.get_user_name() == n; }));
}

name local_context::get_unused_name(name const & prefix, unsigned & idx) const {
    while (true) {
        name curr = prefix.append_after(idx);
        idx++;
        if (!uses_user_name(curr))
            return curr;
    }
}

name local_context::get_unused_name(name const & suggestion) const {
  if (!uses_user_name(suggestion))
        return suggestion;
    unsigned idx = 1;
    return get_unused_name(suggestion, idx);
}

local_context local_context::instantiate_mvars(metavar_context & mctx) const {
    local_context r;
    r.m_next_idx        = m_next_idx;
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            expr new_type = mctx.instantiate_mvars(d.get_type());
            local_decl new_d;
            if (auto v = d.get_value())
                new_d = local_decl(d, new_type, mctx.instantiate_mvars(*v));
            else
                new_d = local_decl(d, new_type);
            r.m_name2local_decl.insert(d.get_name(), new_d);
            r.m_idx2local_decl.insert(d.get_idx(), new_d);
        });
    return r;
}

bool contains_let_local_decl(local_context const & lctx, expr const & e) {
    if (!has_local(e)) return false;
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) {
                if (!is_local(e)) return false;
                optional<local_decl> d = lctx.find_local_decl(e);
                return d && d->get_value();
            }));
}

expr zeta_expand(local_context const & lctx, expr const & e) {
    if (!contains_let_local_decl(lctx, e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_local(e)) return some_expr(e);
            if (is_local(e)) {
                if (auto d = lctx.find_local_decl(e)) {
                    if (auto v = d->get_value())
                        return some_expr(zeta_expand(lctx, *v));
                }
            }
            return none_expr();
        });
}

void initialize_local_context() {
}

void finalize_local_context() {
}
}
