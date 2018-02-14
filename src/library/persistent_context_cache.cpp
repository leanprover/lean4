/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/persistent_context_cache.h"
#include "library/context_cache.h"

namespace lean {
typedef std::pair<token, std::unique_ptr<context_cache>> token_context_cache_pair;

MK_THREAD_LOCAL_GET_DEF(token_context_cache_pair, get_token_context_cache_pair);

persistent_context_cache::persistent_context_cache(token tk, options const & opts) {
    token_context_cache_pair & p = get_token_context_cache_pair();
    if (p.second && p.first == tk && p.second->get_options() == opts) {
        /* Reuse thread local cache */
        m_cache_ptr.swap(p.second);
        m_token = mk_unique_token();
    } else {
        m_cache_ptr.reset(new context_cache(opts));
        m_token     = mk_unique_token();
    }
}

persistent_context_cache::~persistent_context_cache() {
    token_context_cache_pair & p = get_token_context_cache_pair();
    p.first = m_token;
    m_cache_ptr.swap(p.second);
}

options const & persistent_context_cache::get_options() const {
    return m_cache_ptr->get_options();
}

bool persistent_context_cache::get_unfold_lemmas() const {
    return m_cache_ptr->get_unfold_lemmas();
}

unsigned persistent_context_cache::get_nat_offset_cnstr_threshold() const {
    return m_cache_ptr->get_nat_offset_cnstr_threshold();
}

unsigned persistent_context_cache::get_smart_unfolding() const {
    return m_cache_ptr->get_smart_unfolding();
}

unsigned persistent_context_cache::get_class_instance_max_depth() const {
    return m_cache_ptr->get_class_instance_max_depth();
}

optional<declaration> persistent_context_cache::get_decl(type_context & ctx, transparency_mode m, name const & n) {
    return m_cache_ptr->get_decl(ctx, m, n);
}

projection_info const * persistent_context_cache::get_proj_info(type_context & ctx, name const & n) {
    return m_cache_ptr->get_proj_info(ctx, n);
}

bool persistent_context_cache::get_aux_recursor(type_context & ctx, name const & n) {
    return m_cache_ptr->get_aux_recursor(ctx, n);
}

optional<expr> persistent_context_cache::get_infer(expr const & e) {
    return m_cache_ptr->get_infer(e);
}

void persistent_context_cache::set_infer(expr const & e, expr const & t) {
    return m_cache_ptr->set_infer(e, t);
}

bool persistent_context_cache::get_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->get_equiv(m, e1, e2);
}

void persistent_context_cache::set_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->set_equiv(m, e1, e2);
}

bool persistent_context_cache::get_is_def_eq_failure(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->get_is_def_eq_failure(m, e1, e2);
}

void persistent_context_cache::set_is_def_eq_failure(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->set_is_def_eq_failure(m, e1, e2);
}

optional<expr> persistent_context_cache::get_whnf(transparency_mode m, expr const & e) {
    return m_cache_ptr->get_whnf(m, e);
}

void persistent_context_cache::set_whnf(transparency_mode m, expr const & e, expr const & r) {
    return m_cache_ptr->set_whnf(m, e, r);
}

optional<optional<expr>> persistent_context_cache::get_instance(expr const & e) {
    return m_cache_ptr->get_instance(e);
}

void persistent_context_cache::set_instance(expr const & e, optional<expr> const & r) {
    return m_cache_ptr->set_instance(e, r);
}

optional<optional<expr>> persistent_context_cache::get_subsingleton(expr const & e) {
    return m_cache_ptr->get_subsingleton(e);
}

void persistent_context_cache::set_subsingleton(expr const & e, optional<expr> const & r) {
    return m_cache_ptr->set_subsingleton(e, r);
}

void persistent_context_cache::flush_instances() {
    return m_cache_ptr->flush_instances();
}

void persistent_context_cache::reset_frozen_local_instances() {
    return m_cache_ptr->reset_frozen_local_instances();
}

void persistent_context_cache::set_frozen_local_instances(local_instances const & lis) {
    return m_cache_ptr->set_frozen_local_instances(lis);
}

optional<local_instances> persistent_context_cache::get_frozen_local_instances() const {
    return m_cache_ptr->get_frozen_local_instances();
}

optional<fun_info> persistent_context_cache::get_fun_info(type_context & ctx, expr const & e) {
    return m_cache_ptr->get_fun_info(ctx, e);
}

void persistent_context_cache::set_fun_info(type_context & ctx, expr const & e, fun_info const & r) {
    return m_cache_ptr->set_fun_info(ctx, e, r);
}

optional<fun_info> persistent_context_cache::get_fun_info_nargs(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_fun_info_nargs(ctx, e, k);
}

void persistent_context_cache::set_fun_info_nargs(type_context & ctx, expr const & e, unsigned k, fun_info const & r) {
    return m_cache_ptr->set_fun_info_nargs(ctx, e, k, r);
}

optional<unsigned> persistent_context_cache::get_specialization_prefix_size(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialization_prefix_size(ctx, e, k);
}

void persistent_context_cache::set_specialization_prefix_size(type_context & ctx, expr const & e, unsigned k, unsigned r) {
    return m_cache_ptr->set_specialization_prefix_size(ctx, e, k, r);
}

optional<ss_param_infos> persistent_context_cache::get_subsingleton_info(type_context & ctx, expr const & e) {
    return m_cache_ptr->get_subsingleton_info(ctx, e);
}

void persistent_context_cache::set_subsingleton_info(type_context & ctx, expr const & e, ss_param_infos const & r) {
    return m_cache_ptr->set_subsingleton_info(ctx, e, r);
}

optional<ss_param_infos> persistent_context_cache::get_subsingleton_info_nargs(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_subsingleton_info_nargs(ctx, e, k);
}

void persistent_context_cache::set_subsingleton_info_nargs(type_context & ctx, expr const & e, unsigned k, ss_param_infos const & r) {
    return m_cache_ptr->set_subsingleton_info_nargs(ctx, e, k, r);
}

optional<ss_param_infos> persistent_context_cache::get_specialized_subsingleton_info_nargs(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_subsingleton_info_nargs(ctx, e, k);
}

void persistent_context_cache::set_specialization_subsingleton_info_nargs(type_context & ctx, expr const & e, unsigned k, ss_param_infos const & r) {
    return m_cache_ptr->set_specialization_subsingleton_info_nargs(ctx, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_simp_congr_lemma(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_simp_congr_lemma(ctx, e, k);
}

void persistent_context_cache::set_simp_congr_lemma(type_context & ctx, expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_simp_congr_lemma(ctx, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_specialized_simp_congr_lemma(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_simp_congr_lemma(ctx, e, k);
}

void persistent_context_cache::set_specialized_simp_congr_lemma(type_context & ctx, expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_specialized_simp_congr_lemma(ctx, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_congr_lemma(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_congr_lemma(ctx, e, k);
}

void persistent_context_cache::set_congr_lemma(type_context & ctx, expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_congr_lemma(ctx, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_specialized_congr_lemma(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_congr_lemma(ctx, e, k);
}

void persistent_context_cache::set_specialized_congr_lemma(type_context & ctx, expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_specialized_congr_lemma(ctx, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_hcongr_lemma(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_hcongr_lemma(ctx, e, k);
}

void persistent_context_cache::set_hcongr_lemma(type_context & ctx, expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_hcongr_lemma(ctx, e, k, r);
}

optional<app_builder_info> persistent_context_cache::get_app_builder_info(type_context & ctx, expr const & e, unsigned k) {
    return m_cache_ptr->get_app_builder_info(ctx, e, k);
}

void persistent_context_cache::set_app_builder_info(type_context & ctx, expr const & e, unsigned k, app_builder_info const & r) {
    return m_cache_ptr->set_app_builder_info(ctx, e, k, r);
}


optional<app_builder_info> persistent_context_cache::get_app_builder_info(type_context & ctx, expr const & e, list<bool> const & m) {
    return m_cache_ptr->get_app_builder_info(ctx, e, m);
}

void persistent_context_cache::set_app_builder_info(type_context & ctx, expr const & e, list<bool> const & m, app_builder_info const & r) {
    return m_cache_ptr->set_app_builder_info(ctx, e, m, r);
}
}
