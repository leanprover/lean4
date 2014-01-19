/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <functional>
#include "util/lua.h"
#include "util/list.h"
#include "util/splay_tree.h"
#include "util/name.h"
#include "kernel/environment.h"
#include "kernel/formatter.h"

namespace lean {
class rewrite_rule_set;
class rewrite_rule {
    friend class rewrite_rule_set;
    name     m_id;
    expr     m_lhs;
    expr     m_rhs;
    expr     m_ceq;
    expr     m_proof;
    unsigned m_num_args;
    bool     m_is_permutation;
    rewrite_rule(name const & id, expr const & lhs, expr const & rhs, expr const & ceq, expr const & proof,
                 unsigned num_args, bool is_permutation);
public:
    name const & get_id() const { return m_id; }
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    expr const & get_ceq() const { return m_ceq; }
    expr const & get_proof() const { return m_proof; }
    unsigned get_num_args() const { return m_num_args; }
    bool is_permutation() const { return m_is_permutation; }
};

/**
   \brief Actual implementation of the \c rewrite_rule_set class.
*/
class rewrite_rule_set {
    typedef splay_tree<name, name_quick_cmp> name_set;
    ro_environment::weak_ref m_env;
    list<rewrite_rule>       m_rule_set; // TODO(Leo): use better data-structure, e.g., discrimination trees
    name_set                 m_disabled_rules;

    bool enabled(rewrite_rule const & rule) const;
public:
    rewrite_rule_set(ro_environment const & env);
    rewrite_rule_set(rewrite_rule_set const & other);
    ~rewrite_rule_set();

    /**
       \brief Convert the theorem \c th with proof \c proof into conditional rewrite rules, and
       insert the rules into this rule set. The new rules are tagged with the given \c id.
    */
    void insert(name const & id, expr const & th, expr const & proof);

    /**
       \brief Convert the theorem/axiom named \c th_name in the environment into conditional rewrite rules,
       and insert the rules into this rule set. The new rules are tagged with the theorem name.

       This method throws an exception if the environment does not have a theorem/axiom named \c th_name.
    */
    void insert(name const & th_name);

    /** \brief Return true iff the conditional rewrite rules tagged with the given id are enabled. */
    bool enabled(name const & id) const;

    /** \brief Enable/disable the conditional rewrite rules tagged with the given identifier. */
    void enable(name const & id, bool f);

    typedef std::function<bool(rewrite_rule const &)> match_fn; // NOLINT
    typedef std::function<void(rewrite_rule const &, bool)> visit_fn;

    /**
       \brief Execute <tt>fn(rule)</tt> for each (enabled) rule whose the left-hand-side may
       match \c e.
       The traversal is interrupted as soon as \c fn returns true.
    */
    bool find_match(expr const &, match_fn const & fn) const;

    /** \brief Execute <tt>fn(rule, enabled)</tt> for each rule in this rule set. */
    void for_each(visit_fn const & fn) const;

    /** \brief Pretty print this rule set. */
    format pp(formatter const & fmt, options const & opts) const;
};

name const & get_default_rewrite_rule_set_id();
/**
   \brief Create a rewrite rule set inside the given environment.

   \remark The rule set is saved when the environment is serialized.
   \remark This procedure throws an exception if the environment already contains a rule set named \c rule_set_id.
*/
void mk_rewrite_rule_set(environment const & env, name const & rule_set_id = get_default_rewrite_rule_set_id());
/**
   \brief Convert the theorem named \c th_name into conditional rewrite rules
   and insert them in the rule set named \c rule_set_id in the given environment.

   \remark This procedure throws an exception if the environment does not have a theorem/axiom named \c th_name.
   \remark This procedure throws an exception if the environment does not have a rule set named \c rule_set_id.
*/
void add_rewrite_rules(environment const & env, name const & rule_set_id, name const & th_name);
inline void add_rewrite_rules(environment const & env, name const & th_name) {
    add_rewrite_rules(env, get_default_rewrite_rule_set_id(), th_name);
}

/**
   \brief Enable/disable the rewrite rules whose id is \c rule_id in the given rule set.

   \remark This procedure throws an exception if the environment does not have a rule set named \c rule_set_id.
*/
void enable_rewrite_rules(environment const & env, name const & rule_set_id, name const & rule_id, bool flag);
inline void enable_rewrite_rules(environment const & env, name const & rule_id, bool flag) {
    enable_rewrite_rules(env, get_default_rewrite_rule_set_id(), rule_id, flag);
}

/**
   \brief Return the rule set name \c rule_set_id in the given environment.

   \remark This procedure throws an exception if the environment does not have a rule set named \c rule_set_id.
*/
rewrite_rule_set get_rewrite_rule_set(ro_environment const & env, name const & rule_set_id = get_default_rewrite_rule_set_id());
void open_rewrite_rule_set(lua_State * L);
}
