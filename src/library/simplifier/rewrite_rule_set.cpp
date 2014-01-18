/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/splay_tree.h"
#include "util/list_fn.h"
#include "util/sstream.h"
#include "kernel/environment.h"
#include "library/equality.h"
#include "library/simplifier/ceq.h"
#include "library/simplifier/rewrite_rule_set.h"

namespace lean {
/**
   \brief Actual implementation of the \c rewrite_rule_set class.
*/
class rewrite_rule_set::imp {
    typedef splay_tree<name, name_quick_cmp> name_set;
    struct rewrite_rule {
        name m_id;
        expr m_lhs;
        expr m_ceq;
        expr m_proof;
        bool m_is_permutation;
        rewrite_rule(name const & id, expr const & lhs, expr const & ceq, expr const & proof, bool is_permutation):
            m_id(id), m_lhs(lhs), m_ceq(ceq), m_proof(proof), m_is_permutation(is_permutation) {}
    };
    ro_environment::weak_ref m_env;
    list<rewrite_rule>       m_rule_set; // TODO(Leo): use better data-structure, e.g., discrimination trees
    name_set                 m_disabled_rules;

public:
    imp(ro_environment const & env):m_env(env.to_weak_ref()) {}

    void insert(name const & id, expr const & th, expr const & proof) {
        ro_environment env(m_env);
        for (auto const & p : to_ceqs(env, th, proof)) {
            expr const & ceq   = p.first;
            expr const & proof = p.second;
            bool is_perm       = is_permutation_ceq(ceq);
            expr lhs = ceq;
            while (is_pi(lhs)) {
                lhs = abst_body(lhs);
            }
            lean_assert(is_equality(lhs));
            lhs = arg(lhs, num_args(lhs) - 2);
            m_rule_set.emplace_front(id, lhs, ceq, proof, is_perm);
        }
    }

    void insert(name const & th_name) {
        ro_environment env(m_env);
        auto obj = env->find_object(th_name);
        if (obj && (obj->is_theorem() || obj->is_axiom())) {
            insert(th_name, obj->get_type(), mk_constant(th_name));
        } else {
            throw exception(sstream() << "'" << th_name << "' is not a theorem nor an axiom");
        }
    }

    bool enabled(rewrite_rule const & rule) const {
        return !m_disabled_rules.contains(rule.m_id);
    }

    bool enabled(name const & id) const {
        return !m_disabled_rules.contains(id);
    }

    void enable(name const & id, bool f) {
        if (f)
            m_disabled_rules.erase(id);
        else
            m_disabled_rules.insert(id);
    }

    void for_each_match_candidate(expr const &, match_fn const & fn) const {
        auto l = m_rule_set;
        for (auto const & rule : l) {
            if (enabled(rule) && fn(rule.m_lhs, rule.m_ceq, rule.m_is_permutation, rule.m_proof))
                return;
        }
    }

    void for_each(visit_fn const & fn) const {
        auto l = m_rule_set;
        for (auto const & rule : l) {
            fn(rule.m_id, rule.m_ceq, rule.m_proof, enabled(rule));
        }
    }

    format pp(formatter const & fmt, options const & opts) const {
        format r;
        bool first = true;
        unsigned indent = get_pp_indent(opts);
        for_each([&](name const & name, expr const & ceq, expr const &, bool enabled) {
                if (first)
                    first = false;
                else
                    r += line();
                r += format(name);
                if (!enabled)
                    r += format(" [disabled]");
                r += format{space(), colon(), space()};
                r += nest(indent, fmt(ceq, opts));
            });
        return r;
    }
};
rewrite_rule_set::rewrite_rule_set(ro_environment const & env):m_ptr(new imp(env)) {}
rewrite_rule_set::rewrite_rule_set(rewrite_rule_set const & rs):m_ptr(new imp(*(rs.m_ptr))) {}
rewrite_rule_set::~rewrite_rule_set() {}
void rewrite_rule_set::insert(name const & id, expr const & th, expr const & proof) { m_ptr->insert(id, th, proof); }
void rewrite_rule_set::insert(name const & th_name) { m_ptr->insert(th_name); }
bool rewrite_rule_set::enabled(name const & id) const { return m_ptr->enabled(id); }
void rewrite_rule_set::enable(name const & id, bool f) { m_ptr->enable(id, f); }
void rewrite_rule_set::for_each_match_candidate(expr const & e, match_fn const & fn) { m_ptr->for_each_match_candidate(e, fn); }
void rewrite_rule_set::for_each(visit_fn const & fn) { m_ptr->for_each(fn); }
format rewrite_rule_set::pp(formatter const & fmt, options const & opts) const { return m_ptr->pp(fmt, opts); }
}
