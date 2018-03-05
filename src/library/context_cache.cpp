/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context_cache.h"
#include "library/type_context.h"

namespace lean {
context_cache::context_cache():
    context_cacheless() {
}

context_cache::context_cache(options const & o):
    context_cacheless(o) {
}

context_cache::~context_cache() {
}

optional<declaration> context_cache::get_decl(type_context_old & ctx, transparency_mode m, name const & n) {
    auto & cache = m_transparency_cache[static_cast<unsigned>(m)];
    auto it = cache.find(n);
    if (it != cache.end()) {
        return it->second;
    }
    optional<declaration> r = context_cacheless::get_decl(ctx, m, n);
    cache.insert(mk_pair(n, r));
    return r;
}

projection_info const * context_cache::get_proj_info(type_context_old & ctx, name const & n) {
    // TODO(Leo): check if we really need a cache for get_proj_info
    return context_cacheless::get_proj_info(ctx, n);
}

bool context_cache::get_aux_recursor(type_context_old & ctx, name const & n) {
    auto it = m_aux_recursor_cache.find(n);
    if (it != m_aux_recursor_cache.end())
        return it->second;
    bool r = context_cacheless::get_aux_recursor(ctx, n);
    m_aux_recursor_cache.insert(mk_pair(n, r));
    return r;
}

void context_cache::get_unification_hints(type_context_old & ctx, name const & f1, name const & f2, buffer<unification_hint> & hints) {
    if (!m_uhints)
        m_uhints = ::lean::get_unification_hints(ctx.env());
    ::lean::get_unification_hints(*m_uhints, f1, f2, hints);
}

template<typename R, typename C, typename K>
optional<R> find_at(C const & c, K const & e) {
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

optional<fun_info> context_cache::get_fun_info(transparency_mode m, expr const & e) {
    return find_at<fun_info>(m_fi_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_fun_info(transparency_mode m, expr const & e, fun_info const & fi) {
    m_fi_cache[static_cast<unsigned>(m)].insert(mk_pair(e, fi));
}

optional<fun_info> context_cache::get_fun_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<fun_info>(m_fi_cache_nargs[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_fun_info_nargs(transparency_mode m, expr const & e, unsigned nargs, fun_info const & fi) {
    m_fi_cache_nargs[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), fi));
}

optional<unsigned> context_cache::get_specialization_prefix_size(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<unsigned>(m_prefix_cache[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_specialization_prefix_size(transparency_mode m, expr const & e, unsigned nargs, unsigned sz) {
    m_prefix_cache[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), sz));
}

optional<ss_param_infos> context_cache::get_subsingleton_info(transparency_mode m, expr const & e) {
    return find_at<ss_param_infos>(m_ss_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_subsingleton_info(transparency_mode m, expr const & e, ss_param_infos const & ss) {
    m_ss_cache[static_cast<unsigned>(m)].insert(mk_pair(e, ss));
}

optional<ss_param_infos> context_cache::get_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<ss_param_infos>(m_ss_cache_nargs[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs, ss_param_infos const & ss) {
    m_ss_cache_nargs[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), ss));
}

optional<ss_param_infos> context_cache::get_specialized_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<ss_param_infos>(m_ss_cache_spec[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_specialization_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs, ss_param_infos const & ss) {
    m_ss_cache_spec[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), ss));
}
}
