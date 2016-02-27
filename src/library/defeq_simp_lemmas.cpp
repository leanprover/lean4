/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <string>
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "kernel/error_msgs.h"
#include "kernel/instantiate.h"
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/defeq_simp_lemmas.h"
#include "library/util.h"
#include "library/expr_lt.h"
#include "library/scoped_ext.h"
#include "library/tmp_type_context.h"

namespace lean {

/* defeq simp lemmas  */

defeq_simp_lemma::defeq_simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                   list<bool> const & instances, expr const & lhs, expr const & rhs, unsigned priority):
    m_id(id), m_umetas(umetas), m_emetas(emetas), m_instances(instances), m_lhs(lhs), m_rhs(rhs), m_priority(priority) {}

bool operator==(defeq_simp_lemma const & sl1, defeq_simp_lemma const & sl2) {
    return sl1.get_lhs() == sl2.get_lhs() && sl1.get_rhs() == sl2.get_rhs();
}

/* Environment extension */

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct defeq_simp_lemmas_state {
    defeq_simp_lemmas m_defeq_simp_lemmas;
    name_map<unsigned> m_decl_name_to_prio; // Note: redundant but convenient

    void register_defeq_simp_lemma(tmp_type_context & tctx, name const & decl_name, unsigned priority) {
        declaration const & d = tctx.env().get(decl_name);
        // TODO(dhs): once we refactor to register this attribute as "definitions-only", this can be an assert
        if (!d.is_definition()) {
            throw exception("invalid [defeq] simp lemma: must be a definition so that definitional equality can be verified");
        }
        buffer<level> us;
        unsigned num_univs = d.get_num_univ_params();
        for (unsigned i = 0; i < num_univs; i++) {
            us.push_back(tctx.mk_uvar());
        }
        levels ls = to_list(us);
        expr type    = instantiate_type_univ_params(d, ls);
        expr proof   = instantiate_value_univ_params(d, ls);
        return register_defeq_simp_lemma_core(tctx, decl_name, ls, type, proof, priority);
    }

    void register_defeq_simp_lemma_core(tmp_type_context & tctx, name const & decl_name, levels const & umetas,
                                        expr const & type, expr const & proof, unsigned priority) {
        m_decl_name_to_prio.insert(decl_name, priority);
        expr rule = type;
        expr pf = proof;
        buffer<expr> emetas;
        buffer<bool> instances;
        while (is_pi(rule)) {
            expr mvar = tctx.mk_mvar(binding_domain(rule));
            emetas.push_back(mvar);
            instances.push_back(binding_info(rule).is_inst_implicit());
            rule = instantiate(binding_body(rule), mvar);
            pf = binding_body(pf);
        }
        expr lhs, rhs;
        if (!is_eq(rule, lhs, rhs))
            throw exception("invalid [defeq] simp lemma: body must be an equality");
        if (!is_app_of(pf, get_eq_refl_name(), 2) && !is_app_of(pf, get_rfl_name(), 2))
            throw exception("invalid [defeq] simp lemma: proof must be an application of either 'eq.refl' or 'rfl' to two arguments");
        if (lhs == rhs)
            throw exception("invalid [defeq] simp lemma: the two sides of the equality cannot be structurally equal");
        defeq_simp_lemma lemma(decl_name, umetas, to_list(emetas), to_list(instances), lhs, rhs, priority);
        m_defeq_simp_lemmas.insert(lhs, lemma);
    }
};

struct defeq_simp_lemmas_entry {
    name m_decl_name;
    unsigned m_priority;
    defeq_simp_lemmas_entry(name const & decl_name, unsigned priority):
        m_decl_name(decl_name), m_priority(priority) {}
};

struct defeq_simp_lemmas_config {
    typedef defeq_simp_lemmas_entry entry;
    typedef defeq_simp_lemmas_state state;

    static void add_entry(environment const & env, io_state const & ios, state & s, entry const & e) {
        tmp_type_context tctx(env, ios.get_options());
        s.register_defeq_simp_lemma(tctx, e.m_decl_name, e.m_priority);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_decl_name << e.m_priority;
    }
    static entry read_entry(deserializer & d) {
        name decl_name; unsigned prio;
        d >> decl_name >> prio;
        return entry(decl_name, prio);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_decl_name.hash(), e.m_priority));
    }
};

typedef scoped_ext<defeq_simp_lemmas_config> defeq_simp_lemmas_ext;

environment add_defeq_simp_lemma(environment const & env, io_state const & ios, name const & decl_name, unsigned prio, name const & ns, bool persistent) {
    return defeq_simp_lemmas_ext::add_entry(env, ios, defeq_simp_lemmas_entry(decl_name, prio), ns, persistent);
}

bool is_defeq_simp_lemma(environment const & env, name const & decl_name) {
    return defeq_simp_lemmas_ext::get_state(env).m_decl_name_to_prio.contains(decl_name);
}

defeq_simp_lemmas get_defeq_simp_lemmas(environment const & env) {
    return defeq_simp_lemmas_ext::get_state(env).m_defeq_simp_lemmas;
}

defeq_simp_lemmas get_defeq_simp_lemmas(environment const & env, name const & ns) {
    list<defeq_simp_lemmas_entry> const * _entries = defeq_simp_lemmas_ext::get_entries(env, ns);
    defeq_simp_lemmas_state s;
    if (_entries) {
        list<defeq_simp_lemmas_entry> entries = reverse(*_entries);
        for (auto const & e : entries) {
            tmp_type_context tctx(env, get_dummy_ios().get_options());
            s.register_defeq_simp_lemma(tctx, e.m_decl_name, e.m_priority);
        }
    }
    return s.m_defeq_simp_lemmas;
}

/* Pretty printing */

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

format pp_defeq_simp_lemmas(defeq_simp_lemmas const & lemmas, formatter const & fmt, format const & header) {
    format r;
    r += format("defeq simp lemmas");
    r += header + colon() + line();
    lemmas.for_each_entry([&](head_index const &, defeq_simp_lemma const & lemma) {
             r += lemma.pp(fmt) + line();
        });
    return r;
}

/* Setup and teardown */

void initialize_defeq_simp_lemmas() {
    g_class_name    = new name("defeq_simp_lemmas");
    g_key           = new std::string("DEFEQ_SIMP_LEMMAS");

    defeq_simp_lemmas_ext::initialize();

    register_prio_attribute("defeq", "defeq simp lemma",
                            add_defeq_simp_lemma,
                            is_defeq_simp_lemma,
                            [](environment const & env, name const & decl_name) {
                                if (auto p = defeq_simp_lemmas_ext::get_state(env).m_decl_name_to_prio.find(decl_name))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_defeq_simp_lemmas() {
    defeq_simp_lemmas_ext::finalize();
    delete g_key;
    delete g_class_name;
}

}
