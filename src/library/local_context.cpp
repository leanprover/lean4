/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/fresh_name.h"
#include "kernel/for_each_fn.h"
#include "library/local_context.h"
#include "library/pp_options.h"

namespace lean {
static name *       g_local_prefix;
static expr *       g_dummy_type;
static local_decl * g_dummy_decl;

DEF_THREAD_MEMORY_POOL(get_local_decl_allocator, sizeof(local_decl::cell));

void local_decl::cell::dealloc() {
    this->~cell();
    get_local_decl_allocator().recycle(this);
}
local_decl::cell::cell(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi):
    m_name(n), m_pp_name(pp_n), m_type(t), m_value(v), m_bi(bi), m_idx(idx), m_rc(1) {}

local_decl::local_decl():local_decl(*g_dummy_decl) {}
local_decl::local_decl(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi) {
    m_ptr = new (get_local_decl_allocator().allocate()) cell(idx, n, pp_n, t, v, bi);
}

name mk_local_decl_name() {
    return mk_tagged_fresh_name(*g_local_prefix);
}

static expr mk_local_ref(name const & n, name const & pp_n) {
    return mk_local(n, pp_n, *g_dummy_type, binder_info());
}

bool is_local_decl_ref(expr const & e) {
    return is_local(e) && mlocal_type(e) == *g_dummy_type;
}

expr local_decl::mk_ref() const {
    return mk_local_ref(m_ptr->m_name, m_ptr->m_pp_name);
}

bool depends_on(expr const & e, unsigned num, expr const * locals) {
    lean_assert(std::all_of(locals, locals+num, is_local_decl_ref));
    if (!has_local(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (!has_local(e)) return false;
            if (is_local_decl_ref(e) &&
                std::any_of(locals, locals+num,
                            [&](expr const & l) { return mlocal_name(e) == mlocal_name(l); })) {
                found = true;
                return false;
            }
            return true;
        });
    return found;
}

bool depends_on(local_decl const & d, unsigned num, expr const * locals) {
    if (depends_on(d.get_type(), num, locals))
        return true;
    if (auto v = d.get_value())
        return depends_on(*v, num, locals);
    return false;
}

bool depends_on(expr const & e, buffer<expr> const & locals) {
    return depends_on(e, locals.size(), locals.data());
}

bool depends_on(local_decl const & d, buffer<expr> const & locals) {
    return depends_on(d, locals.size(), locals.data());
}

expr local_context::mk_local_decl(name const & n, name const & ppn, expr const & type, optional<expr> const & value, binder_info const & bi) {
    lean_assert(!m_name2local_decl.contains(n));
    unsigned idx = m_next_idx;
    m_next_idx++;
    local_decl l(idx, n, ppn, type, value, bi);
    m_name2local_decl.insert(n, l);
    m_idx2local_decl.insert(idx, l);
    return mk_local_ref(n, ppn);
}

expr local_context::mk_local_decl(expr const & type, binder_info const & bi) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, none_expr(), bi);
}

expr local_context::mk_local_decl(expr const & type, expr const & value) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, some_expr(value), binder_info());
}

expr local_context::mk_local_decl(name const & ppn, expr const & type, binder_info const & bi) {
    return mk_local_decl(mk_local_decl_name(), ppn, type, none_expr(), bi);
}

expr local_context::mk_local_decl(name const & ppn, expr const & type, expr const & value) {
    return mk_local_decl(mk_local_decl_name(), ppn, type, some_expr(value), binder_info());
}

optional<local_decl> local_context::get_local_decl(name const & n) const {
    if (auto r = m_name2local_decl.find(n))
        return optional<local_decl>(*r);
    else
        return optional<local_decl>();
}

optional<local_decl> local_context::get_local_decl(expr const & e) const {
    lean_assert(is_local_decl_ref(e));
    return get_local_decl(mlocal_name(e));
}

void local_context::for_each(std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) { fn(d); });
}

optional<local_decl> local_context::find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

optional<local_decl> local_context::back_find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.back_find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

optional<local_decl> local_context::get_local_decl_from_user_name(name const & n) const {
    return back_find_if([&](local_decl const & d) { return d.get_pp_name() == n; });
}

void local_context::for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each_greater(d.get_idx(), [&](unsigned, local_decl const & d) { return fn(d); });
}

void local_context::pop_local_decl() {
    lean_assert(!m_idx2local_decl.empty());
    local_decl d = m_idx2local_decl.max();
    lean_assert(!m_frozen_decls.contains(d.get_name()));
    m_name2local_decl.erase(d.get_name());
    m_idx2local_decl.erase(d.get_idx());
}

bool local_context::rename_user_name(name const & from, name const & to) {
    if (auto d = get_local_decl_from_user_name(from)) {
        local_decl new_d(d->get_idx(), d->get_name(), to, d->get_type(), d->get_value(), d->get_info());
        m_idx2local_decl.insert(d->get_idx(), new_d);
        m_name2local_decl.insert(d->get_name(), new_d);
        return true;
    } else {
        return false;
    }
}

optional<local_decl> local_context::has_dependencies(local_decl const & d) const {
    lean_assert(get_local_decl(d.get_name()));
    expr l = d.mk_ref();
    optional<local_decl> r;
    for_each_after(d, [&](local_decl const & d2) {
            if (r) return;
            if (depends_on(d2, 1, &l))
                r = d2;
        });
    return r;
}

void local_context::clear(local_decl const & d) {
    lean_assert(get_local_decl(d.get_name()));
    lean_assert(!is_frozen(d.get_name()));
    lean_assert(!has_dependencies(d));
    m_idx2local_decl.erase(d.get_idx());
    m_name2local_decl.erase(d.get_name());
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
                                return is_local_decl_ref(l) && get_local_decl(l);
                            }));
    /* TODO(Leo): check whether the following loop is a performance bottleneck. */
    local_context r = *this;
    for (expr const & l : locals) {
        r.m_name2local_decl.erase(mlocal_name(l));
        r.m_idx2local_decl.erase(get_local_decl(l)->get_idx());
        r.m_frozen_decls.erase(mlocal_name(l));
    }
    lean_assert(r.well_formed());
    return r;
}

/* Return true iff all local_decl references in \c e are in \c s. */
static bool locals_subset_of(expr const & e, name_set const & s) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false; // stop search
            if (is_local_decl_ref(e) && !s.contains(mlocal_name(e))) {
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
            if (is_local_decl_ref(e) && !get_local_decl(e)) {
                ok = false;
                lean_unreachable();
            }
            return true;
        });
    return ok;
}

void local_context::freeze(name const & n) {
    lean_assert(m_name2local_decl.contains(n));
    m_frozen_decls.insert(n);
}

format local_context::pp(formatter const & fmt) const {
    options const & opts = fmt.get_options();
    unsigned indent      = get_pp_indent(opts);
    unsigned max_hs      = get_pp_goal_max_hyps(opts);
    bool first           = true;
    unsigned i           = 0;
    format ids;
    optional<expr> type;
    format r;
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
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

            if (d.get_value()) {
                if (first) first = false;
                else r += comma() + line();
                r += group(format(d.get_pp_name()) + space() + colon() + space() + fmt(d.get_type()) +
                           space() + format(":=") + nest(indent, line() + fmt(*d.get_value())));
            } else if (!type) {
                lean_assert(!d.get_value());
                ids  = format(d.get_pp_name());
                type = d.get_type();
            } else {
                lean_assert(!d.get_value());
                lean_assert(type && d.get_type() == *type);
                ids += space() + format(d.get_pp_name());
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

void initialize_local_context() {
    g_local_prefix = new name(name::mk_internal_unique_name());
    g_dummy_type   = new expr(mk_constant(name::mk_internal_unique_name()));
    g_dummy_decl   = new local_decl(std::numeric_limits<unsigned>::max(),
                                    name("__local_decl_for_default_constructor"), name("__local_decl_for_default_constructor"),
                                    *g_dummy_type, optional<expr>(), binder_info());
}

void finalize_local_context() {
    delete g_local_prefix;
    delete g_dummy_type;
    delete g_dummy_decl;
}
}
