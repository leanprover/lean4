/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/fresh_name.h"
#include "library/local_context.h"

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

expr mk_local_ref(name const & n) {
    return mk_local(n, *g_dummy_type);
}

bool is_local_decl_ref(expr const & e) {
    return is_local(e) && mlocal_type(e) == *g_dummy_type;
}

expr local_context::mk_local_decl(name const & n, name const & ppn, expr const & type, optional<expr> const & value, binder_info const & bi) {
    lean_assert(!m_local_decl_map.contains(n));
    unsigned idx = m_next_idx;
    m_next_idx++;
    local_decl l(idx, n, ppn, type, value, bi);
    m_name2local_decl.insert(n, l);
    m_idx2local_decl.insert(idx, l);
    return mk_local_ref(n);
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

optional<local_decl> local_context::get_local_decl(expr const & e) {
    lean_assert(is_local_decl_ref(e));
    if (auto r = m_name2local_decl.find(mlocal_name(e)))
        return optional<local_decl>(*r);
    else
        return optional<local_decl>();
}

void local_context::for_each(std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) { fn(d); });
}

optional<local_decl> local_context::find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

void local_context::for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each_greater(d.get_idx(), [&](unsigned, local_decl const & d) { return fn(d); });
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
