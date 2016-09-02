/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "kernel/error_msgs.h"
#include "kernel/instantiate.h"
#include "library/attribute_manager.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/type_context.h"
#include "library/tactic/defeq_simplifier/defeq_simp_lemmas.h"

namespace lean {
defeq_simp_lemma::defeq_simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                   list<bool> const & instances, expr const & lhs, expr const & rhs, unsigned priority):
    m_id(id), m_umetas(umetas), m_emetas(emetas), m_instances(instances), m_lhs(lhs), m_rhs(rhs), m_priority(priority) {}

bool operator==(defeq_simp_lemma const & sl1, defeq_simp_lemma const & sl2) {
    return sl1.get_lhs() == sl2.get_lhs() && sl1.get_rhs() == sl2.get_rhs();
}

static void throw_non_rfl_proof() {
    throw exception("invalid [defeq] simp lemma: proof must be an application of either 'eq.refl' or 'rfl'");
}

static void on_add_defeq_simp_lemma(environment const & env, name const & decl_name, bool) {
    type_context ctx(env);
    declaration const & d = env.get(decl_name);
    if (!d.is_definition()) {
        throw exception("invalid [defeq] simp lemma: must be a definition so that definitional equality can be verified");
    }
    expr type = d.get_type();
    expr pf   = d.get_value();
    while (is_pi(type)) {
        if (!is_lambda(pf))
            throw_non_rfl_proof();
        pf   = binding_body(pf);
        type = binding_body(type);
    }
    expr lhs, rhs;
    if (!is_eq(type, lhs, rhs))
        throw exception("invalid [defeq] simp lemma: body must be an equality");
    if (!is_app_of(pf, get_eq_refl_name(), 2) && !is_app_of(pf, get_rfl_name(), 2))
        throw_non_rfl_proof();
    if (lhs == rhs)
        throw exception("invalid [defeq] simp lemma: the two sides of the equality cannot be structurally equal");
}

static void add_lemma_core(tmp_type_context & ctx, name const & decl_name, unsigned priority,
                           defeq_simp_lemmas_ptr & result) {
    environment const & env = ctx.env();
    declaration const & d   = env.get(decl_name);
    lean_assert(d.is_definition());
    buffer<level> umetas;
    unsigned num_univs = d.get_num_univ_params();
    for (unsigned i = 0; i < num_univs; i++) {
        umetas.push_back(ctx.mk_tmp_univ_mvar());
    }
    levels ls = to_list(umetas);
    expr type = instantiate_type_univ_params(d, ls);
    buffer<expr> emetas;
    buffer<bool> instances;
    while (is_pi(type)) {
        expr mvar = ctx.mk_tmp_mvar(binding_domain(type));
        emetas.push_back(mvar);
        instances.push_back(binding_info(type).is_inst_implicit());
        type = instantiate(binding_body(type), mvar);
    }
    expr lhs, rhs;
    lean_verify(is_eq(type, lhs, rhs));
    defeq_simp_lemma lemma(decl_name, to_list(umetas), to_list(emetas), to_list(instances), lhs, rhs, priority);
    result->insert(lhs, lemma);
}

static defeq_simp_lemmas_ptr get_defeq_simp_lemmas_from_attribute(type_context & ctx, name const & attr_name) {
    environment const & env = ctx.env();
    auto const & attr       = get_attribute(env, attr_name);
    buffer<name> lemmas;
    attr.get_instances(env, lemmas);
    defeq_simp_lemmas_ptr result = std::make_shared<defeq_simp_lemmas>();
    unsigned i = lemmas.size();
    while (i > 0) {
        i--;
        name const & id = lemmas[i];
        unsigned prio = attr.get_prio(env, id);
        tmp_type_context tmp_ctx(ctx);
        add_lemma_core(tmp_ctx, id, prio, result);
    }
    return result;
}

static defeq_simp_lemmas_ptr get_defeq_simp_lemmas_from_attribute(environment const & env, name const & attr_name) {
    type_context ctx(env);
    return get_defeq_simp_lemmas_from_attribute(ctx, attr_name);
}

static std::vector<name> * g_defeq_simp_attributes = nullptr;
static defeq_lemmas_token  g_default_token;

defeq_lemmas_token register_defeq_simp_attribute(name const & attr_name) {
    unsigned r = g_defeq_simp_attributes->size();
    g_defeq_simp_attributes->push_back(attr_name);
    register_system_attribute(basic_attribute::with_check(attr_name, "[defeq] simplification lemma",
                                                          on_add_defeq_simp_lemma));
    return r;
}

class defeq_simp_lemmas_cache {
    struct entry {
        environment           m_env;
        name                  m_attr_name;
        unsigned              m_attr_fingerprint;
        defeq_simp_lemmas_ptr m_lemmas;
        entry(environment const & env, name const & attr_name):
            m_env(env), m_attr_name(attr_name), m_attr_fingerprint(0) {}
    };
    std::vector<entry>        m_entries;
public:
    void expand(environment const & env, unsigned new_sz) {
        for (unsigned i = m_entries.size(); i < new_sz; i++) {
            m_entries.emplace_back(env, (*g_defeq_simp_attributes)[i]);
        }
    }

    defeq_simp_lemmas_ptr mk_lemmas(environment const & env, entry & C) {
        lean_trace("defeq_simp_lemmas_cache", tout() << "make defeq simp lemmas [" << C.m_attr_name << "]\n";);
        C.m_env              = env;
        C.m_lemmas           = get_defeq_simp_lemmas_from_attribute(env, C.m_attr_name);
        C.m_attr_fingerprint = get_attribute_fingerprint(env, C.m_attr_name);
        return C.m_lemmas;
    }

    defeq_simp_lemmas_ptr lemmas_of(entry const & C) {
        lean_trace("defeq_simp_lemmas_cache", tout() << "reusing cached defeq simp lemmas [" << C.m_attr_name << "]\n";);
        return C.m_lemmas;
    }

    defeq_simp_lemmas_ptr get(environment const & env, defeq_lemmas_token token) {
        lean_assert(token < g_defeq_simp_attributes->size());
        if (token >= m_entries.size()) expand(env, token+1);
        lean_assert(token < m_entries.size());
        entry & C = m_entries[token];
        if (!C.m_lemmas) return mk_lemmas(env, C);
        if (is_eqp(env, C.m_env)) return lemmas_of(C);
        if (!env.is_descendant(C.m_env) ||
            get_attribute_fingerprint(env, C.m_attr_name) != C.m_attr_fingerprint) {
            lean_trace("defeq_simp_lemmas_cache",
                       bool c = (get_attribute_fingerprint(env, C.m_attr_name) == C.m_attr_fingerprint);
                       tout() << "creating new cache, is_descendant: " << env.is_descendant(C.m_env)
                       << ", attribute fingerprint compatibility: " << c << "\n";);
            return mk_lemmas(env, C);
        }
        return lemmas_of(C);
    }
};

MK_THREAD_LOCAL_GET_DEF(defeq_simp_lemmas_cache, get_cache);

defeq_simp_lemmas_ptr get_defeq_simp_lemmas(environment const & env) {
    return get_cache().get(env, g_default_token);
}

defeq_simp_lemmas_ptr get_defeq_simp_lemmas(environment const & env, defeq_lemmas_token token) {
    return get_cache().get(env, token);
}

format defeq_simp_lemma::pp(formatter const & fmt) const {
    format r;
    r += format("#") + format(get_num_emeta());
    if (get_priority() != LEAN_DEFAULT_PRIORITY)
        r += space() + paren(format(get_priority()));
    format r1 = comma() + space() + fmt(get_lhs());
    r1       += space() + format("↦") + pp_indent_expr(fmt, get_rhs());
    r += group(r1);
    return r;
}

format pp_defeq_simp_lemmas(defeq_simp_lemmas const & lemmas, formatter const & fmt) {
    format r;
    r += format("defeq simp lemmas") + colon() + line();
    lemmas.for_each_entry([&](head_index const &, defeq_simp_lemma const & lemma) {
             r += lemma.pp(fmt) + line();
        });
    return r;
}

void initialize_defeq_simp_lemmas() {
    register_trace_class("defeq_simp_lemmas_cache");
    g_defeq_simp_attributes = new std::vector<name>();
    g_default_token         = register_defeq_simp_attribute("defeq");
}

void finalize_defeq_simp_lemmas() {
    delete g_defeq_simp_attributes;
}
}
