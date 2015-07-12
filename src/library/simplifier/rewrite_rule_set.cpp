/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "library/scoped_ext.h"
#include "library/expr_pair.h"
#include "library/relation_manager.h"
#include "library/simplifier/ceqv.h"
#include "library/simplifier/rewrite_rule_set.h"

namespace lean {
bool operator==(rewrite_rule const & r1, rewrite_rule const & r2) {
    return r1.m_lhs == r2.m_lhs && r1.m_rhs == r2.m_rhs;
}

rewrite_rule::rewrite_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
                           expr const & lhs, expr const & rhs, expr const & proof, bool is_perm):
    m_id(id), m_univ_metas(univ_metas), m_metas(metas), m_lhs(lhs), m_rhs(rhs), m_proof(proof),
    m_is_permutation(is_perm) {}

format rewrite_rule::pp(formatter const & fmt) const {
    format r;
    r += format("#") + format(length(m_metas));
    if (m_is_permutation)
        r += space() + format("perm");
    format r1 = comma() + space() + fmt(m_lhs);
    r1       += space() + format("↦") + pp_indent_expr(fmt, m_rhs);
    r += group(r1);
    return r;
}

rewrite_rule_set::rewrite_rule_set(name const & eqv):
    m_eqv(eqv) {}

void rewrite_rule_set::insert(rewrite_rule const & r) {
    m_set.insert(r.get_lhs(), r);
}

list<rewrite_rule> const * rewrite_rule_set::find(head_index const & h) const {
    return m_set.find(h);
}

void rewrite_rule_set::for_each(std::function<void(rewrite_rule const &)> const & fn) const {
    m_set.for_each_entry([&](head_index const &, rewrite_rule const & r) { fn(r); });
}

void rewrite_rule_set::erase(rewrite_rule const & r) {
    m_set.erase(r.get_lhs(), r);
}

void rewrite_rule_sets::insert(name const & eqv, rewrite_rule const & r) {
    rewrite_rule_set s(eqv);
    if (auto const * curr = m_sets.find(eqv)) {
        s = *curr;
    }
    s.insert(r);
    m_sets.insert(eqv, s);
}

void rewrite_rule_sets::erase(name const & eqv, rewrite_rule const & r) {
    if (auto const * curr = m_sets.find(eqv)) {
        rewrite_rule_set s = *curr;
        s.erase(r);
        if (s.empty())
            m_sets.erase(eqv);
        else
            m_sets.insert(eqv, s);
    }
}

void rewrite_rule_sets::get_relations(buffer<name> & rs) const {
    m_sets.for_each([&](name const & r, rewrite_rule_set const &) {
            rs.push_back(r);
        });
}

rewrite_rule_set const * rewrite_rule_sets::find(name const & eqv) const {
    return m_sets.find(eqv);
}

list<rewrite_rule> const * rewrite_rule_sets::find(name const & eqv, head_index const & h) const {
    if (auto const * s = m_sets.find(eqv))
        return s->find(h);
    return nullptr;
}

void rewrite_rule_sets::for_each(std::function<void(name const &, rewrite_rule const &)> const & fn) const {
    m_sets.for_each([&](name const & eqv, rewrite_rule_set const & s) {
            s.for_each([&](rewrite_rule const & r) {
                    fn(eqv, r);
                });
        });
}

static name * g_prefix = nullptr;

rewrite_rule_sets add_core(type_checker & tc, rewrite_rule_sets const & s,
                           name const & id, levels const & univ_metas, expr const & e, expr const & h) {
    list<expr_pair> ceqvs   = to_ceqvs(tc, e, h);
    environment const & env = tc.env();
    rewrite_rule_sets new_s = s;
    for (expr_pair const & p : ceqvs) {
        expr new_e = p.first;
        expr new_h = p.second;
        bool is_perm       = is_permutation_ceqv(env, new_e);
        buffer<expr> metas;
        unsigned idx = 0;
        while (is_pi(new_e)) {
            expr mvar = mk_metavar(name(*g_prefix, idx), binding_domain(new_e));
            idx++;
            metas.push_back(mvar);
            new_e = instantiate(binding_body(new_e), mvar);
        }
        expr rel, lhs, rhs;
        if (is_transitive(env, new_e, rel, lhs, rhs) && is_constant(rel)) {
            new_s.insert(const_name(rel), rewrite_rule(id, univ_metas, to_list(metas), lhs, rhs, new_h, is_perm));
        }
    }
    return new_s;
}

rewrite_rule_sets add(type_checker & tc, rewrite_rule_sets const & s, name const & id, expr const & e, expr const & h) {
    return add_core(tc, s, id, list<level>(), e, h);
}

rewrite_rule_sets join(rewrite_rule_sets const & s1, rewrite_rule_sets const & s2) {
    rewrite_rule_sets new_s1 = s1;
    s2.for_each([&](name const & eqv, rewrite_rule const & r) {
            new_s1.insert(eqv, r);
        });
    return new_s1;
}

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct rrs_state {
    rewrite_rule_sets           m_sets;
    name_set                    m_rnames;
    name_map<rewrite_rule_sets> m_namespace_cache;

    void add(environment const & env, name const & cname) {
        type_checker tc(env);
        declaration const & d = env.get(cname);
        buffer<level> us;
        unsigned num_univs = d.get_num_univ_params();
        for (unsigned i = 0; i < num_univs; i++) {
            us.push_back(mk_meta_univ(name(*g_prefix, i)));
        }
        levels ls = to_list(us);
        expr e    = instantiate_type_univ_params(d, ls);
        expr h    = mk_constant(cname, ls);
        m_sets = add_core(tc, m_sets, cname, ls, e, h);
        m_rnames.insert(cname);
        m_namespace_cache.erase(get_namespace(env));
    }
};

struct rrs_config {
    typedef name       entry;
    typedef rrs_state  state;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        s.add(env, e);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e;
    }
    static entry read_entry(deserializer & d) {
        entry e; d >> e; return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.hash());
    }
};

template class scoped_ext<rrs_config>;
typedef scoped_ext<rrs_config> rrs_ext;

environment add_rewrite_rule(environment const & env, name const & n, bool persistent) {
    return rrs_ext::add_entry(env, get_dummy_ios(), n, persistent);
}

bool is_rewrite_rule(environment const & env, name const & n) {
    return rrs_ext::get_state(env).m_rnames.contains(n);
}

rewrite_rule_sets get_rewrite_rule_sets(environment const & env) {
    return rrs_ext::get_state(env).m_sets;
}

void initialize_rewrite_rule_set() {
    g_prefix     = new name(name::mk_internal_unique_name());
    g_class_name = new name("rrs");
    g_key        = new std::string("rrs");
    rrs_ext::initialize();
}

void finalize_rewrite_rule_set() {
    rrs_ext::finalize();
    delete g_key;
    delete g_class_name;
    delete g_prefix;
}
}
