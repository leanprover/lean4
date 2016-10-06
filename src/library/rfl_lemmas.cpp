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
#include "library/rfl_lemmas.h"

namespace lean {
rfl_lemma::rfl_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                     list<bool> const & instances, expr const & lhs, expr const & rhs, unsigned priority):
    m_id(id), m_umetas(umetas), m_emetas(emetas), m_instances(instances), m_lhs(lhs), m_rhs(rhs), m_priority(priority) {}

bool operator==(rfl_lemma const & sl1, rfl_lemma const & sl2) {
    return sl1.get_lhs() == sl2.get_lhs() && sl1.get_rhs() == sl2.get_rhs();
}

static void throw_non_rfl_proof() {
    throw exception("invalid reflexivity lemma: proof must be an application of either 'eq.refl' or 'rfl'");
}

static void on_add_rfl_lemma(environment const & env, name const & decl_name, bool) {
    type_context ctx(env);
    declaration const & d = env.get(decl_name);
    if (!d.is_definition()) {
        throw exception("invalid reflexivity lemma: must be a definition so that definitional equality can be verified");
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
        throw exception("invalid reflexivity lemma: body must be an equality");
    if (!is_app_of(pf, get_eq_refl_name(), 2) && !is_app_of(pf, get_rfl_name(), 2))
        throw_non_rfl_proof();
    if (lhs == rhs)
        throw exception("invalid reflexivity lemma: the two sides of the equality cannot be structurally equal");
}

static void add_lemma_core(tmp_type_context & ctx, name const & decl_name, unsigned priority,
                           rfl_lemmas & result) {
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
    rfl_lemma lemma(decl_name, to_list(umetas), to_list(emetas), to_list(instances), lhs, rhs, priority);
    result.insert(lhs, lemma);
}

static rfl_lemmas get_rfl_lemmas_from_attribute(type_context & ctx, name const & attr_name) {
    environment const & env = ctx.env();
    auto const & attr       = get_attribute(env, attr_name);
    buffer<name> lemmas;
    attr.get_instances(env, lemmas);
    rfl_lemmas result;
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

static rfl_lemmas get_rfl_lemmas_from_attribute(environment const & env, name const & attr_name) {
    type_context ctx(env);
    return get_rfl_lemmas_from_attribute(ctx, attr_name);
}

static std::vector<name> * g_rfl_lemmas_attributes = nullptr;
static rfl_lemmas_token    g_default_token;

rfl_lemmas_token register_defeq_simp_attribute(name const & attr_name) {
    unsigned r = g_rfl_lemmas_attributes->size();
    g_rfl_lemmas_attributes->push_back(attr_name);
    register_system_attribute(basic_attribute::with_check(attr_name, "reflexivity lemma",
                                                          on_add_rfl_lemma));
    return r;
}

class rfl_lemmas_cache {
    struct entry {
        environment          m_env;
        name                 m_attr_name;
        unsigned             m_attr_fingerprint;
        optional<rfl_lemmas> m_lemmas;
        entry(environment const & env, name const & attr_name):
            m_env(env), m_attr_name(attr_name), m_attr_fingerprint(0) {}
    };
    std::vector<entry>        m_entries;
public:
    void expand(environment const & env, unsigned new_sz) {
        for (unsigned i = m_entries.size(); i < new_sz; i++) {
            m_entries.emplace_back(env, (*g_rfl_lemmas_attributes)[i]);
        }
    }

    rfl_lemmas mk_lemmas(environment const & env, entry & C) {
        lean_trace("rfl_lemmas_cache", tout() << "make reflexivity lemmas [" << C.m_attr_name << "]\n";);
        C.m_env              = env;
        C.m_lemmas           = get_rfl_lemmas_from_attribute(env, C.m_attr_name);
        C.m_attr_fingerprint = get_attribute_fingerprint(env, C.m_attr_name);
        return *C.m_lemmas;
    }

    rfl_lemmas lemmas_of(entry const & C) {
        lean_trace("rfl_lemmas_cache", tout() << "reusing cached reflexivity lemmas [" << C.m_attr_name << "]\n";);
        return *C.m_lemmas;
    }

    rfl_lemmas get(environment const & env, rfl_lemmas_token token) {
        lean_assert(token < g_rfl_lemmas_attributes->size());
        if (token >= m_entries.size()) expand(env, token+1);
        lean_assert(token < m_entries.size());
        entry & C = m_entries[token];
        if (!C.m_lemmas) return mk_lemmas(env, C);
        if (is_eqp(env, C.m_env)) return lemmas_of(C);
        if (!env.is_descendant(C.m_env) ||
            get_attribute_fingerprint(env, C.m_attr_name) != C.m_attr_fingerprint) {
            lean_trace("rfl_lemmas_cache",
                       bool c = (get_attribute_fingerprint(env, C.m_attr_name) == C.m_attr_fingerprint);
                       tout() << "creating new cache, is_descendant: " << env.is_descendant(C.m_env)
                       << ", attribute fingerprint compatibility: " << c << "\n";);
            return mk_lemmas(env, C);
        }
        return lemmas_of(C);
    }
};

MK_THREAD_LOCAL_GET_DEF(rfl_lemmas_cache, get_cache);

rfl_lemmas get_rfl_lemmas(environment const & env) {
    return get_cache().get(env, g_default_token);
}

rfl_lemmas get_rfl_lemmas(environment const & env, rfl_lemmas_token token) {
    return get_cache().get(env, token);
}

format rfl_lemma::pp(formatter const & fmt) const {
    format r;
    r += format(m_id) + space() + format("#") + format(get_num_emeta());
    if (get_priority() != LEAN_DEFAULT_PRIORITY)
        r += space() + paren(format("prio:") + space() + format(get_priority()));
    format r1 = comma() + space() + fmt(get_lhs());
    r1       += space() + format("↦") + pp_indent_expr(fmt, get_rhs());
    r += group(r1);
    return r;
}

format pp_rfl_lemmas(rfl_lemmas const & lemmas, formatter const & fmt) {
    format r;
    r += format("reflexivity lemmas") + colon() + line();
    lemmas.for_each_entry([&](head_index const &, rfl_lemma const & lemma) {
             r += lemma.pp(fmt) + line();
        });
    return r;
}


static bool instantiate_emetas(type_context & ctx, list<expr> const & _emetas, list<bool> const & _instances) {
    buffer<expr> emetas;
    buffer<bool> instances;
    to_buffer(_emetas, emetas);
    to_buffer(_instances, instances);

    lean_assert(emetas.size() == instances.size());
    for (unsigned i = 0; i < emetas.size(); ++i) {
        expr m = emetas[i];
        unsigned mvar_idx = emetas.size() - 1 - i;
        expr m_type = ctx.instantiate_mvars(ctx.infer(m));
        // TODO(Leo, Daniel): do we need the following assertion?
        // lean_assert(!has_expr_metavar(m_type));
        if (ctx.get_tmp_mvar_assignment(mvar_idx)) continue;
        if (instances[i]) {
            if (auto v = ctx.mk_class_instance(m_type)) {
                if (!ctx.is_def_eq(m, *v)) {
                    lean_trace(name({"rfl_lemma", "failure"}),
                               tout() << "unable to assign instance for: " << m_type << "\n";);
                    return false;
                } else {
                    lean_assert(ctx.get_tmp_mvar_assignment(mvar_idx));
                    continue;
                }
            } else {
                lean_trace(name({"rfl_lemma", "failure"}),
                           tout() << "unable to synthesize instance for: " << m_type << "\n";);
                return false;
            }
        } else {
            lean_trace(name({"rfl_lemma", "failure"}),
                       tout() << "failed to assign: " << m << " : " << m_type << "\n";);
            return false;
        }
    }
    return true;
}

expr rfl_lemma_rewrite(type_context & ctx, expr const & e, rfl_lemma const & sl) {
    type_context::tmp_mode_scope scope(ctx, sl.get_num_umeta(), sl.get_num_emeta());
    if (!ctx.is_def_eq(e, sl.get_lhs())) return e;

    lean_trace("rfl_lemma",
               expr new_lhs = ctx.instantiate_mvars(sl.get_lhs());
               expr new_rhs = ctx.instantiate_mvars(sl.get_rhs());
               tout() << "(" << sl.get_id() << ") "
               << "[" << new_lhs << " --> " << new_rhs << "]\n";);

    if (!instantiate_emetas(ctx, sl.get_emetas(), sl.get_instances())) return e;

    for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
        if (!ctx.get_tmp_uvar_assignment(i)) return e;
    }

    return ctx.instantiate_mvars(sl.get_rhs());
}

void initialize_rfl_lemmas() {
    register_trace_class("rfl_lemmas_cache");
    register_trace_class("rfl_lemma");
    register_trace_class(name{"rfl_lemma", "failure"});
    g_rfl_lemmas_attributes = new std::vector<name>();
    g_default_token         = register_defeq_simp_attribute("defeq");
}

void finalize_rfl_lemmas() {
    delete g_rfl_lemmas_attributes;
}
}
