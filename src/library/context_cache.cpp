/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context_cache.h"

namespace lean {
context_cache::context_cache():
    context_cacheless() {
}

context_cache::context_cache(options const & o):
    context_cacheless(o) {
}

context_cache::~context_cache() {
}

optional<declaration> context_cache::get_decl(type_context & ctx, transparency_mode m, name const & n) {
    auto & cache = m_transparency_cache[static_cast<unsigned>(m)];
    auto it = cache.find(n);
    if (it != cache.end()) {
        return it->second;
    }
    optional<declaration> r = context_cacheless::get_decl(ctx, m, n);
    cache.insert(mk_pair(n, r));
    return r;
}

projection_info const * context_cache::get_proj_info(type_context & ctx, name const & n) {
    // TODO(Leo): check if we really need a cache for get_proj_info
    return context_cacheless::get_proj_info(ctx, n);
}

bool context_cache::get_aux_recursor(type_context & ctx, name const & n) {
    auto it = m_aux_recursor_cache.find(n);
    if (it != m_aux_recursor_cache.end())
        return it->second;
    bool r = context_cacheless::get_aux_recursor(ctx, n);
    m_aux_recursor_cache.insert(mk_pair(n, r));
    return r;
}

template<typename R, typename C>
optional<R> find_at(C const & c, expr const & e) {
    auto it = c.find(e);
    if (it != c.end())
        return optional<R>(it->second);
    else
        return optional<R>();
}

optional<expr> context_cache::get_infer(expr const & e) {
    return find_at<expr>(m_infer_cache, e);
}

void context_cache::set_infer(expr const & e, expr const & ty) {
    m_infer_cache.insert(mk_pair(e, ty));
}

bool context_cache::get_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_equiv_manager[static_cast<unsigned>(m)].is_equiv(e1, e2);
}

void context_cache::set_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    m_equiv_manager[static_cast<unsigned>(m)].add_equiv(e1, e2);
}

bool context_cache::get_is_def_eq_failure(transparency_mode m, expr const & t, expr const & s) {
    auto const & fcache = m_failure_cache[static_cast<unsigned>(m)];
    if (t.hash() < s.hash()) {
        return fcache.find(mk_pair(t, s)) != fcache.end();
    } else if (t.hash() > s.hash()) {
        return fcache.find(mk_pair(s, t)) != fcache.end();
    } else {
        return
            fcache.find(mk_pair(t, s)) != fcache.end() ||
            fcache.find(mk_pair(s, t)) != fcache.end();
    }
}

void context_cache::set_is_def_eq_failure(transparency_mode m, expr const & t, expr const & s) {
    auto & fcache = m_failure_cache[static_cast<unsigned>(m)];
    if (t.hash() <= s.hash())
        fcache.insert(mk_pair(t, s));
    else
        fcache.insert(mk_pair(s, t));
}

optional<expr> context_cache::get_whnf(transparency_mode m, expr const & e) {
    return find_at<expr>(m_whnf_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_whnf(transparency_mode m, expr const & e, expr const & r) {
    m_whnf_cache[static_cast<unsigned>(m)].insert(mk_pair(e, r));
}

optional<optional<expr>> context_cache::get_instance(expr const & e) {
    return find_at<optional<expr>>(m_instance_cache, e);
}

void context_cache::set_instance(expr const & e, optional<expr> const & r) {
    m_instance_cache.insert(mk_pair(e, r));
}

optional<optional<expr>> context_cache::get_subsingleton(expr const & e) {
    return find_at<optional<expr>>(m_subsingleton_cache, e);
}

void context_cache::set_subsingleton(expr const & e, optional<expr> const & r) {
    m_subsingleton_cache.insert(mk_pair(e, r));
}

void context_cache::flush_instances() {
    m_instance_cache.clear();
    m_subsingleton_cache.clear();
}
}
