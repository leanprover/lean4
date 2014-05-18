/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "util/sstream.h"
#include "util/list_fn.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/find_fn.h"

namespace lean {
namespace inductive {
static name g_tmp_prefix = name::mk_internal_unique_name();

environment add_inductive(environment const & env, name const & ind_name, level_param_names const & level_params,
                          unsigned num_params, expr const & type, list<intro_rule> const & intro_rules) {
    return add_inductive(env, level_params, num_params, list<inductive_decl>(inductive_decl(ind_name, type, intro_rules)));
}

struct add_inductive_fn {
    environment          m_env;
    level_param_names    m_level_names;
    unsigned             m_num_params;
    list<inductive_decl> m_decls;
    unsigned             m_decls_sz;
    list<level>          m_levels; // m_level_names ==> m_levels
    name_generator       m_ngen;
    type_checker         m_tc;

    buffer<expr>         m_param_types;
    buffer<expr>         m_param_consts;
    buffer<level>        m_it_levels;    // the levels for each inductive datatype in m_decls
    buffer<expr>         m_it_consts;    // the constants for each inductive datatype in m_decls
    buffer<unsigned>     m_it_num_args;  // total number of arguments (params + indices) for each inductive datatype in m_decls

    add_inductive_fn(environment                  env,
                     level_param_names const &    level_params,
                     unsigned                     num_params,
                     list<inductive_decl> const & decls):
        m_env(env), m_level_names(level_params), m_num_params(num_params), m_decls(decls),
        m_ngen(g_tmp_prefix), m_tc(m_env) {
        m_decls_sz = length(m_decls);
        m_levels = map2<level>(level_params, [](name const & n) { return mk_param_univ(n); });
    }

    /** \brief Return the number of inductive datatypes being defined. */
    unsigned get_num_its() const { return m_decls_sz; }

    /** \brief Make sure the latest environment is being used by m_tc */
    void updt_type_checker() {
        type_checker tc(m_env);
        m_tc.swap(tc);
    }

    /** \brief Display types being declared */
    void display(std::ostream & out) {
        out << "\nadd_inductive\n";
        if (!is_nil(m_level_names)) {
            out << "level params: ";
            for (auto l : m_level_names) { out << l << " "; }
            out << "\n";
        }
        out << "num params: " << m_num_params << "\n";
        for (auto d : m_decls) {
            out << inductive_decl_name(d) << " : " << inductive_decl_type(d) << "\n";
            for (auto ir : inductive_decl_intros(d)) {
                out << "  " << intro_rule_name(ir) << " : " << intro_rule_type(ir) << "\n";
            }
        }
    }

    name mk_fresh_name() { return m_ngen.next(); }

    /** \brief Create a local constant for the given binding. */
    expr mk_local_for(expr const & b) {
        return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b));
    }

    /**
       \brief Check if the type of datatypes is well typed, all inductive datatypes have the same parameters,
       and the number of parameters match the argument num_params.

       This method also populates the fields m_param_types and m_param_consts, m_it_levels, m_it_consts.
    */
    void check_inductive_types() {
        bool first   = true;
        bool to_prop = false; // set to true if the inductive datatypes live in Bool/Prop (Type 0)
        for (auto d : m_decls) {
            expr t = inductive_decl_type(d);
            m_tc.check(t, m_level_names);
            unsigned i  = 0;
            m_it_num_args.push_back(0);
            while (is_pi(t)) {
                if (i < m_num_params) {
                    if (first) {
                        m_param_types.push_back(binding_domain(t));
                        expr l = mk_local_for(t);
                        m_param_consts.push_back(l);
                        t = instantiate(binding_body(t), l);
                    } else {
                        if (!m_tc.is_def_eq(binding_domain(t), m_param_types[i]))
                            throw kernel_exception(m_env, "parameters of all inductive datatypes must match");
                        t = instantiate(binding_body(t), m_param_consts[i]);
                    }
                    i++;
                } else {
                    t = binding_body(t);
                }
                m_it_num_args.back()++;
            }
            if (i != m_num_params)
                throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");
            t = m_tc.ensure_sort(t);
            if (m_env.impredicative()) {
                // if the environment is impredicative, then the resultant universe is 0 (Bool/Prop),
                // or is never zero (under any parameter assignment).
                if (!is_zero(sort_level(t)) && !is_not_zero(sort_level(t)))
                    throw kernel_exception(m_env,
                                           "the resultant universe must be 0 or different"
                                           "from zero for all parameter/global level assignments");
                if (first) {
                    to_prop = is_zero(sort_level(t));
                } else {
                    if (is_zero(sort_level(t)) != to_prop)
                        throw kernel_exception(m_env,
                                               "for impredicative environments, if one datatype is in Bool/Prop, "
                                               "then all of them must be in Bool/Prop");
                }
            }
            m_it_levels.push_back(sort_level(t));
            m_it_consts.push_back(mk_constant(inductive_decl_name(d), m_levels));
            first = false;
        }
    }

    /** \brief Add all datatype declarations to environment. */
    void declare_inductive_types() {
        for (auto d : m_decls) {
            m_env = m_env.add(check(m_env, mk_var_decl(inductive_decl_name(d), m_level_names, inductive_decl_type(d))));
        }
        updt_type_checker();
    }

    /**
        \brief Return true iff \c t is a term of ther form
             (I As t)
        where I is the d_idx inductive datatype being declared and
        As are the global parameters of this declaration.
    */
    bool is_valid_it_app(expr const & t, unsigned d_idx) {
        buffer<expr> args;
        expr I = get_app_args(t, args);
        if (!m_tc.is_def_eq(I, m_it_consts[d_idx]) || args.size() != m_it_num_args[d_idx])
            return false;
        for (unsigned i = 0; i < m_num_params; i++) {
            if (m_param_consts[i] != args[i])
                return false;
        }
        return true;
    }

    /** \brief Return true iff \c t is a valid occurrence of one of the datatypes being defined. */
    bool is_valid_it_app(expr const & t) {
        for (unsigned i = 0; i < get_num_its(); i++)
            if (is_valid_it_app(t, i))
                return true;
        return false;
    }

    /** \brief Return true iff \c e is one of the inductive datatype being declared. */
    bool is_it_occ(expr const & e) {
        return
            is_constant(e) &&
            std::any_of(m_it_consts.begin(), m_it_consts.end(), [&](expr const & c) { return const_name(e) == const_name(c); });
    }

    /** \brief Return true if \c t does not contain any occurrence of a datatype being declared */
    bool has_it_occ(expr const & t) {
        return (bool)find(t, [&](expr const & e, unsigned) { return is_it_occ(e); }); // NOLINT
    }

    /**
       \brief Check if \c t contains only positive occurrences of the inductive datatypes being declared.
       Return true iff it is a recursive argument.
    */
    bool check_positivity(expr t, name const & intro_name, int arg_idx) {
        t = m_tc.whnf(t);
        if (!has_it_occ(t)) {
            return false; // nonrecursive argument
        } else if (is_pi(t)) {
            if (has_it_occ(binding_domain(t)))
                throw kernel_exception(m_env, sstream() << "arg #" << arg_idx << " of '" << intro_name << "' "
                                       "has a non positive occurrence of the datatypes being declared");
            return check_positivity(instantiate(binding_body(t), mk_local_for(t)), intro_name, arg_idx);
        } else if (is_valid_it_app(t)) {
            return true; // recursive argument
        } else {
            throw kernel_exception(m_env, sstream() << "arg #" << arg_idx << " of '" << intro_name << "' "
                                   "contain a non valid occurrence of the datatypes being declared");
        }
    }

    /**
       \brief Check the intro_rule \c ir of the given inductive decl. \c d_idx is the position of \c d in m_decls.

       \see check_intro_rules
    */
    void check_intro_rule(inductive_decl const &, unsigned d_idx, intro_rule const & ir) {
        expr t = intro_rule_type(ir);
        name n = intro_rule_name(ir);
        m_tc.check(t, m_level_names);
        unsigned i     = 0;
        bool found_rec = false;
        while (is_pi(t)) {
            if (i < m_num_params) {
                if (!m_tc.is_def_eq(binding_domain(t), m_param_types[i]))
                    throw kernel_exception(m_env, sstream() << "arg #" << i << " of '" << n << "' "
                                           << "does not match inductive datatypes parameters'");
                t = instantiate(binding_body(t), m_param_consts[i]);
            } else {
                expr s = m_tc.ensure_sort(m_tc.infer(binding_domain(t)));
                // the sort is ok IF
                //   1- its level is <= inductive datatype level, OR
                //   2- m_env is impredicative and inductive datatype is at level 0
                if (!(is_geq(m_it_levels[d_idx], sort_level(s)) || (is_zero(m_it_levels[d_idx]) && m_env.impredicative())))
                    throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << i << ") "
                                           << "of '" << n << "' is too big for the corresponding inductive datatype");
                bool is_rec = check_positivity(binding_domain(t), n, i);
                if (found_rec && !is_rec)
                    throw kernel_exception(m_env, sstream() << "arg #" << i << " of '" << n << "' "
                                           << "is not recursive, but it occurs after recursive arguments");
                if (is_rec)
                    found_rec = true;
                if (!found_rec) {
                    t = instantiate(binding_body(t), mk_local_for(t));
                } else {
                    t = binding_body(t);
                    if (!closed(t))
                        throw kernel_exception(m_env, sstream() << "invalid occurrence of recursive arg#" << i <<
                                               " of '" << n << "' the body of the functional type depends on it.");
                }
            }
            i++;
        }
        if (!is_valid_it_app(t, d_idx))
            throw kernel_exception(m_env, sstream() << "invalid return type for '" << n << "'");
    }

    /**
        \brief Check if
           - all introduction rules start with the same parameters
           - the type of all arguments (which are not datatype global params) live in universes <= level of the corresponding datatype
           - all inductive datatype occurrences are positive
           - all introduction rules are well typed

        \remark this method must be executed after declare_inductive_types
    */
    void check_intro_rules() {
        unsigned i = 0;
        for (auto d : m_decls) {
            for (auto ir : inductive_decl_intros(d))
                check_intro_rule(d, i, ir);
            i++;
        }
    }

    /** \brief Add all introduction rules (aka constructors) to environment */
    void declare_intro_rules() {
        for (auto d : m_decls) {
            for (auto ir : inductive_decl_intros(d))
                m_env = m_env.add(check(m_env, mk_var_decl(intro_rule_name(ir), m_level_names, intro_rule_type(ir))));
        }
    }

    environment operator()() {
        display(std::cout);
        if (get_num_its() == 0)
            throw kernel_exception(m_env, "at least one inductive datatype declaration expected");
        check_inductive_types();
        declare_inductive_types();
        check_intro_rules();
        declare_intro_rules();
        return m_env;
    }
};

environment add_inductive(environment                  env,
                          level_param_names const &    level_params,
                          unsigned                     num_params,
                          list<inductive_decl> const & decls) {
    return add_inductive_fn(env, level_params, num_params, decls)();
}
}
}
