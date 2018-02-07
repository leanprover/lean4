/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/list_fn.h"
#include "util/rb_map.h"
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"

/* The implementation is based on the paper: "Inductive Families", Peter Dybjer, 1997
   The main differences are:
      - Support for Prop (when environment is marked as impredicative)
      - Universe levels

   The support for Prop is based on the paper: "Inductive Definitions in the System Coq: Rules and Properties",
   Christine Paulin-Mohring.

   The kernel does not support mutually inductive types anymore. We simulate them using indexed families outside of the kernel.

   Given a sequence of universe levels parameters (m_level_names), a datatype decl is of the form
         I : (A :: \sigma) (a :: \alpha[A]), Type.{l_k}
             I is the name of the k-th inductive datatype
             A is the sequence of global parameters (it must have size m_num_params)
             a is the sequence of indices

   Each inductive declaration has a sequence of introduction rules of the form
         intro_i : (A :: \sigma) (b :: \beta[A]) (u :: \gama[A, b]), I A p[A, b]
               A is the sequence of global parameters (it must have size m_num_params)
               b is the sequence of non-recursive arguments (i.e., they do not include any I)
               u is the sequence of recursive arguments (they contain positive occurrences of I
         each u_i, in the sequence u, is of the form
               x :: \Epsilon[A, b], I A p_i[A, b, x]

         Remark: we don't enforce that all b arguments occur before all u arguments.

         Again, all introduction rules must have the same sequence of global parameters

   The universe levels of arguments b and u must be smaller than or equal to l_k in I.

   When the environment is marked as impredicative, then l_k must be 0 (Prop) or must be different from zero for
   any instantiation of the universe level parameters (and global level parameters).

   This module produces an eliminator/recursor for the inductive datatype I.
   The eliminator has an extra univese level parameter when
          1- Type.{0} is not impredicative in the given environment
          2- l_k is never zero (for any universe level assignment)
          3- There is only one introduction rule
   Let l' be this extra universe level, in the following rules, and 0 if none of the conditions above hold.

        elim : (A :: \sigma)
               (C :: (a :: \alpha[A]) (c : I A a), Type.{l'})
               (e :: \epsilon[A])
               (a :: \alpha[A])
               (n :: I A a),
             C_k a n

          A is the sequence of global parameters
          C is a type former (aka the motive).
          e is the sequence of minor premises. The size of the sequence is equal to the sum of the length of all introduction rules.
          a is the sequence of indices, it is equal to sequence occurring in I
          n is the major premise

    The minor premise e_j : \epsilon_j[A] in (e:: \epsilon[A]) corresponds to the j-th introduction rule in the inductive
    datatype I.

       \epsilon_j[A] : (b :: \beta[A]) (u :: \gama[A, b]) (v :: \delta[A, b]), C p[A, b] intro_j A b u

           b and u are the corresponding arguments in intro_j. \delta[A, b] has the same length of \gama[A, b],
           and \delta[A, b] is (x :: \Epsilon[A, b]), C p[A, b, x] (u x)


     When the environment is impredicative and l_k is zero, then we use nondependent elimination, and we omit
     the argument c in C, and v in the minor premises. That is, C becomes
            (C :: (a :: \alpha[A]), Type.{l'})
     and \epsilon_i_j[A]
            \epsilon_i_j[A] : (b :: \beta[A]) (u :: \gama[A, b]), C p[A, b]

     Finally, this module also generate computational rules for the extended normalizer. Actually, we only generate
     the right hand side for the rules. They have the form

        Fun (A, C, e, b, u), elim A C e p[A,b] (intro_i A b u) ==> Fun (A, C, e, b, u), (e_i b u v)
*/
namespace lean {
namespace inductive {
static name * g_ind_fresh           = nullptr; /* prefix for fresh names created in this module. */
static name * g_inductive_extension = nullptr;

/** \brief Environment extension used to store the computational rules associated with inductive datatype declarations. */
struct inductive_env_ext : public environment_extension {
    struct elim_info {
        name              m_inductive_name; // name of the inductive datatype associated with eliminator
        level_param_names m_level_names; // level parameter names used in computational rule
        unsigned          m_num_params;  // number of global parameters A
        unsigned          m_num_ACe;     // sum of number of global parameters A, type former C, and minor preimises e.
        unsigned          m_num_indices; // number of inductive datatype indices
        /** \brief We support K-like reduction when the inductive datatype is in Type.{0} (aka Prop), proof irrelevance
            is enabled, it has only one introduction rule, the introduction rule has "0 arguments".
            Example: equality defined as

            inductive eq {A : Type} (a : A) : A -> Prop :=
            refl : eq a a

            satisfies these requirements when proof irrelevance is enabled.
            Another example is heterogeneous equality. */
        bool              m_K_target;
        /** \brief m_dep_elim == true, if dependent elimination is used for this eliminator */
        bool              m_dep_elim;
        elim_info() {}
        elim_info(name const & id_name, level_param_names const & ls, unsigned num_ps, unsigned num_ACe, unsigned num_indices,
                  bool is_K_target, bool dep_elim):
            m_inductive_name(id_name), m_level_names(ls), m_num_params(num_ps), m_num_ACe(num_ACe),
            m_num_indices(num_indices), m_K_target(is_K_target), m_dep_elim(dep_elim) {}
    };

    struct comp_rule {
        name              m_elim_name;     // name of the corresponding eliminator
        unsigned          m_num_bu;        // sum of number of arguments u and v in the corresponding introduction rule.
        expr              m_comp_rhs;      // computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
        expr              m_comp_rhs_body; // body of m_comp_rhs:  (e_k_i b u v)
        comp_rule() {}
        comp_rule(name const & e, unsigned num_bu, expr const & rhs):
            m_elim_name(e), m_num_bu(num_bu), m_comp_rhs(rhs), m_comp_rhs_body(rhs) {
            while (is_lambda(m_comp_rhs_body))
                m_comp_rhs_body = binding_body(m_comp_rhs_body);
        }
    };

    // mapping from introduction rule name to computation rule data
    name_map<elim_info>             m_elim_info;
    name_map<comp_rule>             m_comp_rules;
    // mapping from intro rule to datatype
    name_map<name>                  m_intro_info;
    name_map<inductive_decl>        m_inductive_info;

    inductive_env_ext() {}

    void add_elim(name const & n, name const & id_name, level_param_names const & ls,
                  unsigned num_ps, unsigned num_ace, unsigned num_indices, bool is_K_target,
                  bool dep_elim) {
        m_elim_info.insert(n, elim_info(id_name, ls, num_ps, num_ace, num_indices, is_K_target, dep_elim));
    }

    void add_comp_rhs(name const & n, name const & e, unsigned num_bu, expr const & rhs) {
        m_comp_rules.insert(n, comp_rule(e, num_bu, rhs));
    }

    void add_intro_info(name const & ir_name, name const & id_name) {
        m_intro_info.insert(ir_name, id_name);
    }

    void add_inductive_info(inductive_decl const & d) {
        m_inductive_info.insert(d.m_name, d);
    }
};

/** \brief Auxiliary object for registering the environment extension */
struct inductive_env_ext_reg {
    unsigned m_ext_id;
    inductive_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<inductive_env_ext>()); }
};

static inductive_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static inductive_env_ext const & get_extension(environment const & env) {
    return static_cast<inductive_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, inductive_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<inductive_env_ext>(ext));
}

/**\ brief Return recursor name */
name get_elim_name(name const & n) {
    return n + name("rec");
}

environment certified_inductive_decl::add_constant(environment const & env, name const & n, level_param_names const & ls,
                                                   expr const & t) const {
    return env.add(certify_unchecked::certify_or_check(env, mk_constant_assumption(n, ls, t, m_is_trusted)));
}

environment certified_inductive_decl::add_core(environment const & env, bool update_ext_only) const {
    environment new_env = env;
    inductive_env_ext ext(get_extension(new_env));
    // declare inductive types
    if (!update_ext_only)
        new_env = add_constant(new_env, m_decl.m_name, m_decl.m_level_params, m_decl.m_type);
    ext.add_inductive_info(m_decl);
    // declare introduction rules
    for (auto ir : m_decl.m_intro_rules) {
        if (!update_ext_only)
            new_env = add_constant(new_env, intro_rule_name(ir), m_decl.m_level_params, intro_rule_type(ir));
        ext.add_intro_info(intro_rule_name(ir), m_decl.m_name);
    }
    // declare elimination rules
    name elim_name = get_elim_name(m_decl.m_name);
    if (!update_ext_only)
        new_env = add_constant(new_env, elim_name, m_elim_levels, m_elim_type);
    ext.add_elim(elim_name, m_decl.m_name, m_elim_levels, m_decl.m_num_params,
                 m_num_ACe, m_num_indices, m_K_target, m_dep_elim);
    list<comp_rule> rules = m_comp_rules;
    for (auto ir : m_decl.m_intro_rules) {
        comp_rule const & rule = head(rules);
        ext.add_comp_rhs(intro_rule_name(ir), elim_name, rule.m_num_bu, rule.m_comp_rhs);
        rules = tail(rules);
    }
    return update(new_env, ext);
}

environment certified_inductive_decl::add(environment const & env) const {
    if (env.trust_lvl() == 0) {
        return add_inductive(env, m_decl, m_is_trusted).first;
    } else {
        return add_core(env, false);
    }
}

/** \brief Helper functional object for processing inductive datatype declarations. */
struct add_inductive_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    environment          m_env;
    name_generator       m_name_generator;
    inductive_decl       m_decl;
    // when kernel sets Type.{0} as impredicative, then
    // we track whether the resultant universe cannot be zero for any
    // universe level instantiation
    bool                 m_is_not_zero;
    list<level>          m_levels;       // m_decl.m_level_params ==> m_levels
    type_checker_ptr     m_tc;

    level                m_elim_level;   // extra universe level for eliminator.
    bool                 m_dep_elim;     // true if using dependent elimination

    buffer<expr>         m_param_consts; // local constants used to represent global parameters
    level                m_it_level;     // resultant level
    expr                 m_it_const;     // the constants for inductive datatype
    unsigned             m_it_num_args;  // number of arguments (params + indices) for inductive datatype

    struct elim_info {
        expr             m_C;              // type former constant
        buffer<expr>     m_indices;        // local constant for each index
        expr             m_major_premise;  // major premise for each inductive decl
        buffer<expr>     m_minor_premises; // minor premise for each introduction rule
        bool             m_K_target;
        elim_info():m_K_target(false) {}
    };
    elim_info            m_elim_info; // for datatype being declared
    bool                 m_is_trusted;

    add_inductive_fn(environment            env,
                     inductive_decl const & decl,
                     bool is_trusted):
        m_env(env), m_name_generator(*g_ind_fresh), m_decl(decl),
        m_tc(new type_checker(m_env, true, false)) {
        m_is_not_zero = false;
        m_levels      = param_names_to_levels(decl.m_level_params);
        m_is_trusted  = is_trusted;
    }

    /** \brief Make sure the latest environment is being used by m_tc. */
    void updt_type_checker() {
        m_tc.reset(new type_checker(m_env, true, false));
    }

    type_checker & tc() { return *(m_tc.get()); }
    bool is_def_eq(expr const & t, expr const & s) { return tc().is_def_eq(t, s); }
    expr whnf(expr const & e) { return tc().whnf(e); }
    expr ensure_type(expr const & e) { return tc().ensure_type(e); }

    /** \brief Create a local constant for the given binding. */
    expr mk_local_for(expr const & b) { return mk_local(m_name_generator.next(), binding_name(b), binding_domain(b), binding_info(b)); }

    /** \brief Return type of the i-th global parameter. */
    expr get_param_type(unsigned i) { return mlocal_type(m_param_consts[i]); }

    /** \brief Check if the type of datatype is well typed,
        and the number of parameters match the argument num_params.

        This method also populates the fields m_param_consts, m_elim_info.m_indices, m_it_level, m_it_const. */
    void check_inductive_type() {
        expr t       = m_decl.m_type;
        tc().check(t, m_decl.m_level_params);
        unsigned i    = 0;
        m_it_num_args = 0;
        t = whnf(t);
        while (is_pi(t)) {
            if (i < m_decl.m_num_params) {
                expr l = mk_local_for(t);
                m_param_consts.push_back(l);
                t = instantiate(binding_body(t), l);
                i++;
            } else {
                expr c = mk_local_for(t);
                m_elim_info.m_indices.push_back(c);
                t = instantiate(binding_body(t), c);
            }
            t = whnf(t);
            m_it_num_args++;
        }
        if (i != m_decl.m_num_params)
            throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");
        t = tc().ensure_sort(t);
        // We track whether the resultant universe
        // is never zero (under any parameter assignment).
        // TODO(Leo): when the resultant universe may be 0 and not zero depending on parameter assignment,
        // we may generate two recursors: one when it is 0, and another one when it is not.
        m_is_not_zero = is_not_zero(sort_level(t));
        m_it_level = sort_level(t);
        m_it_const = mk_constant(m_decl.m_name, m_levels);
    }

    /** \brief Add all datatype declarations to environment. */
    void declare_inductive_type() {
        m_env = m_env.add(check(m_env, mk_constant_assumption(m_decl.m_name, m_decl.m_level_params, m_decl.m_type,
                                                              m_is_trusted)));
        updt_type_checker();
    }

    /** \brief Return true iff \c e is the inductive datatype being declared. */
    bool is_it_occ(expr const & e) {
        return is_constant(e) && const_name(e) == const_name(m_it_const);
    }

    /** \brief Return true if \c t does not contain any occurrence of a datatype being declared. */
    bool has_it_occ(expr const & t) {
        return (bool)find(t, [&](expr const & e, unsigned) { return is_it_occ(e); }); // NOLINT
    }

    /** \brief Return true iff \c t is a term of the form (I As t)
        where I is the inductive datatype being defined, and As are the
        global parameters of this declaration. Moreover I does not occur in t */
    bool is_valid_it_app(expr const & t) {
        buffer<expr> args;
        expr I = get_app_args(t, args);
        if (!is_def_eq(I, m_it_const) || args.size() != m_it_num_args)
            return false;
        unsigned i = 0;
        for (; i < m_decl.m_num_params; i++) {
            if (m_param_consts[i] != args[i])
                return false;
        }
        for (; i < args.size(); i++) {
            if (has_it_occ(args[i]))
                return false;
        }
        return true;
    }

    /** \brief Return some(d_idx) iff \c t is a recursive argument, \c d_idx is the index of the recursive inductive datatype.
        Return none otherwise. */
    bool is_rec_argument(expr t) {
        t = whnf(t);
        while (is_pi(t))
            t = whnf(instantiate(binding_body(t), mk_local_for(t)));
        return is_valid_it_app(t);
    }

    /** \brief Check if \c t contains only positive occurrences of the inductive datatypes being declared. */
    void check_positivity(expr t, name const & intro_name, int arg_idx) {
        t = whnf(t);
        if (!has_it_occ(t)) {
            // nonrecursive argument
        } else if (is_pi(t)) {
            if (has_it_occ(binding_domain(t)))
                throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << intro_name << "' "
                                       "has a non positive occurrence of the datatypes being declared");
            check_positivity(instantiate(binding_body(t), mk_local_for(t)), intro_name, arg_idx);
        } else if (is_valid_it_app(t)) {
            // recursive argument
        } else {
            throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << intro_name << "' "
                                   "contains a non valid occurrence of the datatypes being declared");
        }
    }

    /** \brief Check the intro_rule \c ir.
        \see check_intro_rules */
    void check_intro_rule(intro_rule const & ir) {
        expr t = intro_rule_type(ir);
        name n = intro_rule_name(ir);
        /* make sure intro rule type does not contain locals nor metavariables. */
        check_no_mlocal(m_env, n, t, true);
        tc().check(t, m_decl.m_level_params);
        unsigned i     = 0;
        bool found_rec = false;
        while (is_pi(t)) {
            if (i < m_decl.m_num_params) {
                if (!is_def_eq(binding_domain(t), get_param_type(i)))
                    throw kernel_exception(m_env, sstream() << "arg #" << (i + 1) << " of '" << n << "' "
                                           << "does not match inductive datatypes parameters'");
                t = instantiate(binding_body(t), m_param_consts[i]);
            } else {
                expr s = ensure_type(binding_domain(t));
                // the sort is ok IF
                //   1- its level is <= inductive datatype level, OR
                //   2- inductive datatype is at level 0
                if (!(is_geq(m_it_level, sort_level(s)) || is_zero(m_it_level)))
                    throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << (i + 1) << ") "
                                           << "of '" << n << "' is too big for the corresponding inductive datatype");
                if (m_is_trusted)
                    check_positivity(binding_domain(t), n, i);
                bool is_rec = (bool)is_rec_argument(binding_domain(t)); // NOLINT
                if (is_rec)
                    found_rec = true;
                if (!found_rec) {
                    t = instantiate(binding_body(t), mk_local_for(t));
                } else {
                    t = binding_body(t);
                    if (!closed(t))
                        throw kernel_exception(m_env, sstream() << "invalid occurrence of recursive arg#" << (i+1) <<
                                               " of '" << n << "', the body of the functional type depends on it.");
                }
            }
            i++;
        }
        if (!is_valid_it_app(t))
            throw kernel_exception(m_env, sstream() << "invalid return type for '" << n << "'");
    }

    /** \brief Check if
        - all introduction rules start with the same parameters
        - the type of all arguments (which are not datatype global params) live in universes <= level of the corresponding datatype
        - inductive datatype occurrences are positive
        - all introduction rules are well typed

        \remark this method must be executed after declare_inductive_types */
    void check_intro_rules() {
        for (auto ir : m_decl.m_intro_rules)
            check_intro_rule(ir);
    }

    /** \brief Add all introduction rules (aka constructors) to environment. */
    void declare_intro_rules() {
        for (auto ir : m_decl.m_intro_rules) {
            m_env = m_env.add(check(m_env, mk_constant_assumption(intro_rule_name(ir),
                                                                  m_decl.m_level_params, intro_rule_type(ir),
                                                                  m_is_trusted)));
        }
        updt_type_checker();
    }

    /** \brief Return true if type former C in the recursor can only map to Type.{0} */
    bool elim_only_at_universe_zero() {
        if (m_is_not_zero) {
            // If Type.{0} is not impredicative or the resultant inductive datatype is not in Type.{0},
            // then the recursor may return Type.{l} where l is a universe level parameter.
            return false;
        }
        unsigned num_intros = length(m_decl.m_intro_rules);
        if (num_intros > 1) {
            // If we have more than one introduction rule, then yes, the type former can only
            // map to Type.{0}
            return true;
        }
        if (num_intros == 0) {
            // if we don't have intro rules, then we don't need to check anything else
            return false;
        }
        // We have only one introduction rule, the final check is, the type of each argument
        // that is not a parameter:
        //  1- It must live in Type.{0}, *OR*
        //  2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
        //     We can justify 2 by observing that this information is not a *secret* it is part of the type.
        //     By eliminating to a non-proposition, we would not be revealing anything that is not already known.
        auto ir    = head(m_decl.m_intro_rules);
        expr t     = intro_rule_type(ir);
        unsigned i = 0;
        buffer<expr> to_check; // arguments that we must check if occur in the result type
        while (is_pi(t)) {
            expr local = mk_local_for(t);
            if (i >= m_decl.m_num_params) {
                expr s = ensure_type(binding_domain(t));
                if (!is_zero(sort_level(s))) {
                    // Current argument is not in Type.{0} (i.e., condition 1 failed).
                    // We save it in to_check to be able to try condition 2 above.
                    to_check.push_back(local);
                }
            }
            t = instantiate(binding_body(t), local);
            i++;
        }
        buffer<expr> result_args;
        get_app_args(t, result_args);
        // Check condition 2: every argument in to_check must occur in result_args
        for (expr const & arg : to_check) {
            if (std::find(result_args.begin(), result_args.end(), arg) == result_args.end())
                return true; // condition 2 failed
        }
        return false;
    }

    /** \brief Initialize m_elim_level. */
    void mk_elim_level() {
        if (elim_only_at_universe_zero()) {
            // environment is impredicative, datatype maps to Prop, we have more than one introduction rule.
            m_elim_level = mk_level_zero();
        } else {
            name l("l");
            int i = 1;
            while (std::find(m_decl.m_level_params.begin(), m_decl.m_level_params.end(), l) != m_decl.m_level_params.end()) {
                l = name("l").append_after(i);
                i++;
            }
            m_elim_level = mk_param_univ(l);
        }
    }

    /** \brief Initialize m_dep_elim flag. */
    void set_dep_elim() {
        if (is_zero(m_it_level))
            m_dep_elim = false;
        else
            m_dep_elim = true;
    }

    /** \brief Given t of the form (I As is) where I is the inductive datatypes being defined,
        As are the global parameters, and is the actual indices provided to it.
        Store `is` in the argument \c indices. */
    void get_I_indices(expr const & t, buffer<expr> & indices) {
        lean_assert(is_valid_it_app(t));
        buffer<expr> all_args;
        get_app_args(t, all_args);
        for (unsigned i = m_decl.m_num_params; i < all_args.size(); i++)
            indices.push_back(all_args[i]);
    }

    /** \brief Populate m_elim_info. */
    void mk_elim_info() {
        // First, populate the fields m_C and m_major_premise
        m_elim_info.m_major_premise = mk_local(m_name_generator.next(), "n",
                                               mk_app(mk_app(m_it_const, m_param_consts), m_elim_info.m_indices), binder_info());
        expr C_ty = mk_sort(m_elim_level);
        if (m_dep_elim)
            C_ty = Pi(m_elim_info.m_major_premise, C_ty);
        C_ty = Pi(m_elim_info.m_indices, C_ty);
        name C_name("C");
        m_elim_info.m_C = mk_local(m_name_generator.next(), C_name, C_ty, binder_info());

        // Populate the field m_minor_premises
        unsigned minor_idx = 1;
        // A declaration is target for K-like reduction when
        // it has one intro, the intro has 0 arguments, proof irrelevance is enabled,
        // and it is a proposition.
        // In the following for-loop we check if the intro rule
        // has 0 arguments.
        bool is_K_target =
            is_zero(m_it_level) &&             // It is a Prop
            length(m_decl.m_intro_rules) == 1; // datatype has only one intro rule
        for (auto ir : m_decl.m_intro_rules) {
            buffer<expr> b_u; // nonrec and rec args
            buffer<expr> u;   // rec args
            buffer<expr> v;   // inductive args
            expr t     = intro_rule_type(ir);
            unsigned i = 0;
            while (is_pi(t)) {
                if (i < m_decl.m_num_params) {
                    t = instantiate(binding_body(t), m_param_consts[i]);
                } else {
                    is_K_target = false; // See comment before for-loop.
                    expr l = mk_local_for(t);
                    b_u.push_back(l);
                    if (is_rec_argument(binding_domain(t)))
                        u.push_back(l);
                    t = instantiate(binding_body(t), l);
                }
                i++;
            }
            buffer<expr> it_indices;
            get_I_indices(t, it_indices);
            expr C_app      = mk_app(m_elim_info.m_C, it_indices);
            if (m_dep_elim) {
                expr intro_app  = mk_app(mk_app(mk_constant(intro_rule_name(ir), m_levels), m_param_consts), b_u);
                C_app = mk_app(C_app, intro_app);
            }
            // populate v using u
            for (unsigned i = 0; i < u.size(); i++) {
                expr u_i    = u[i];
                expr u_i_ty = whnf(mlocal_type(u_i));
                buffer<expr> xs;
                while (is_pi(u_i_ty)) {
                    expr x = mk_local_for(u_i_ty);
                    xs.push_back(x);
                    u_i_ty = whnf(instantiate(binding_body(u_i_ty), x));
                }
                buffer<expr> it_indices;
                get_I_indices(u_i_ty, it_indices);
                expr C_app  = mk_app(m_elim_info.m_C, it_indices);
                if (m_dep_elim) {
                    expr u_app  = mk_app(u_i, xs);
                    C_app = mk_app(C_app, u_app);
                }
                expr v_i_ty = Pi(xs, C_app);
                name ih("ih");
                if (u.size() > 1) {
                    name const & u_i_name = mlocal_pp_name(u_i);
                    if (u_i_name.is_atomic() && u_i_name.is_string()) {
                        ih = ih.append_after("_").append_after(u_i_name.get_string());
                    } else {
                        ih = ih.append_after(i+1);
                    }
                }
                expr v_i    = mk_local(m_name_generator.next(), ih, v_i_ty, binder_info());
                v.push_back(v_i);
            }
            expr minor_ty = Pi(b_u, Pi(v, C_app));
            expr minor = mk_local(m_name_generator.next(), name("e").append_after(minor_idx), minor_ty, binder_info());
            m_elim_info.m_minor_premises.push_back(minor);
            minor_idx++;
        }
        m_elim_info.m_K_target = is_K_target;
    }

    /** \brief Return the name of the eliminator/recursor for the type being defined . */
    name get_elim_name() { return ::lean::inductive::get_elim_name(m_decl.m_name); }

    /** \brief Return the level parameter names for the eliminator. */
    level_param_names get_elim_level_param_names() {
        if (is_param(m_elim_level))
            return level_param_names(param_id(m_elim_level), m_decl.m_level_params);
        else
            return m_decl.m_level_params;
    }

    /** \brief Return the levels for the eliminator application. */
    levels get_elim_level_params() {
        if (is_param(m_elim_level))
            return levels(m_elim_level, m_levels);
        else
            return m_levels;
    }

    /** \brief Declare elimination rule. */
    expr declare_elim_rule_core() {
        elim_info const & info = m_elim_info;
        expr C_app   = mk_app(info.m_C, info.m_indices);
        if (m_dep_elim)
            C_app = mk_app(C_app, info.m_major_premise);
        expr elim_ty = Pi(info.m_major_premise, C_app);
        elim_ty      = Pi(info.m_indices, elim_ty);
        // abstract all introduction rules
        unsigned j = m_elim_info.m_minor_premises.size();
        while (j > 0) {
            --j;
            elim_ty = Pi(m_elim_info.m_minor_premises[j], elim_ty);
        }
        // abstract motive
        elim_ty   = Pi(m_elim_info.m_C, elim_ty);
        // parameters
        elim_ty   = Pi(m_param_consts, elim_ty);
        elim_ty   = infer_implicit(elim_ty, true /* strict */);
        m_env = m_env.add(check(m_env, mk_constant_assumption(get_elim_name(), get_elim_level_param_names(), elim_ty,
                                                              m_is_trusted)));
        return elim_ty;
    }

    /** \brief Declare the eliminator/recursor. */
    expr declare_elim_rule() {
        set_dep_elim();
        mk_elim_level();
        mk_elim_info();
        expr r = declare_elim_rule_core();
        updt_type_checker();
        return r;
    }

    /** \brief Create computional rules RHS, and return certified_inductive_decl object. */
    certified_inductive_decl mk_certified_decl(expr const & elim_type) {
        unsigned minor_idx = 0;
        expr C = m_elim_info.m_C;
        buffer<expr> e; e.append(m_elim_info.m_minor_premises);
        levels ls = get_elim_level_params();
        buffer<certified_inductive_decl::comp_rule> comp_rules;
        for (auto ir : m_decl.m_intro_rules) {
            buffer<expr> b_u; // nonrec and rec arguments
            buffer<expr> u;   // rec arguments only
            expr t = intro_rule_type(ir);
            unsigned i = 0;
            while (is_pi(t)) {
                if (i < m_decl.m_num_params) {
                    t = instantiate(binding_body(t), m_param_consts[i]);
                } else {
                    expr l = mk_local_for(t);
                    b_u.push_back(l);
                    if (is_rec_argument(binding_domain(t)))
                        u.push_back(l);
                    t = instantiate(binding_body(t), l);
                }
                i++;
            }
            buffer<expr> v;
            for (unsigned i = 0; i < u.size(); i++) {
                expr u_i    = u[i];
                expr u_i_ty = whnf(mlocal_type(u_i));
                buffer<expr> xs;
                while (is_pi(u_i_ty)) {
                    expr x = mk_local_for(u_i_ty);
                    xs.push_back(x);
                    u_i_ty = whnf(instantiate(binding_body(u_i_ty), x));
                }
                buffer<expr> it_indices;
                get_I_indices(u_i_ty, it_indices);
                expr elim_app = mk_constant(get_elim_name(), ls);
                elim_app = mk_app(mk_app(mk_app(mk_app(mk_app(elim_app, m_param_consts), C), e), it_indices), mk_app(u_i, xs));
                v.push_back(Fun(xs, elim_app));
            }
            expr e_app = mk_app(mk_app(e[minor_idx], b_u), v);
            expr comp_rhs   = Fun(m_param_consts, Fun(C, Fun(e, Fun(b_u, e_app))));
            tc().check(comp_rhs, get_elim_level_param_names());
            comp_rules.emplace_back(b_u.size(), comp_rhs);
            minor_idx++;
        }
        bool elim_Prop = !is_param(m_elim_level);
        return certified_inductive_decl(m_decl.m_num_params + 1 + e.size(), elim_Prop, m_dep_elim,
                                        get_elim_level_param_names(), elim_type, m_decl,
                                        m_elim_info.m_K_target, m_elim_info.m_indices.size(), to_list(comp_rules),
                                        m_is_trusted);
    }

    pair<environment, certified_inductive_decl> operator()() {
        check_inductive_type();
        declare_inductive_type();
        check_intro_rules();
        declare_intro_rules();
        certified_inductive_decl c = mk_certified_decl(declare_elim_rule());
        m_env = c.add_core(m_env, true);
        return mk_pair(m_env, c);
    }
};

pair<environment, certified_inductive_decl>
add_inductive(environment env, inductive_decl const & decl, bool is_trusted) {
    if (!env.norm_ext().supports(*g_inductive_extension))
        throw kernel_exception(env, "environment does not support inductive datatypes");
    return add_inductive_fn(env, decl, is_trusted)();
}

bool inductive_normalizer_extension::supports(name const & feature) const {
    return feature == *g_inductive_extension;
}

/** \brief Return true if \c e is an introduction rule for an eliminator named \c elim */
static inductive_env_ext::comp_rule const * is_intro_for(inductive_env_ext const & ext, name const & elim, expr const & e) {
    expr const & intro_fn  = get_app_fn(e);
    if (!is_constant(intro_fn))
        return nullptr;
    auto it = ext.m_comp_rules.find(const_name(intro_fn));
    if (it && it->m_elim_name == elim)
        return it;
    else
        return nullptr;
}

/** \brief If \c d_name is the name of a non-empty inductive datatype, then return the
    name of the first introduction rule. Return none otherwise. */
static optional<name> get_first_intro(environment const & env, name const & d_name) {
    inductive_env_ext const & ext = get_extension(env);
    if (inductive_decl const * decl = ext.m_inductive_info.find(d_name)) {
        auto intros = decl->m_intro_rules;
        if (intros)
            return optional<name>(intro_rule_name(head(intros)));
    }
    return optional<name>();
}

static optional<expr> mk_nullary_intro(environment const & env, expr const & type, unsigned num_params) {
    buffer<expr> args;
    expr const & d = get_app_args(type, args);
    if (!is_constant(d))
        return none_expr();
    name const & d_name = const_name(d);
    auto intro_name = get_first_intro(env, d_name);
    if (!intro_name)
        return none_expr();
    args.shrink(num_params);
    return some(mk_app(mk_constant(*intro_name, const_levels(d)), args));
}

// For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
// to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
static optional<expr> to_intro_when_K(inductive_env_ext::elim_info const * it,
                                      expr const & e, abstract_type_context & ctx) {
    lean_assert(it->m_K_target);
    environment const & env = ctx.env();
    expr app_type    = ctx.whnf(ctx.infer(e));
    expr const & app_type_I = get_app_fn(app_type);
    if (!is_constant(app_type_I) || const_name(app_type_I) != it->m_inductive_name)
        return none_expr(); // type incorrect
    if (has_expr_metavar(app_type)) {
        buffer<expr> app_type_args;
        get_app_args(app_type, app_type_args);
        for (unsigned i = it->m_num_params; i < app_type_args.size(); i++) {
            if (has_expr_metavar(app_type_args[i]))
                return none_expr();
        }
    }
    auto new_intro_app = mk_nullary_intro(env, app_type, it->m_num_params);
    if (!new_intro_app)
        return none_expr();
    expr new_type    = ctx.infer(*new_intro_app);
    if (!ctx.is_def_eq(app_type, new_type))
        return none_expr();
    return new_intro_app;
}

optional<expr> inductive_normalizer_extension::operator()(expr const & e, abstract_type_context & ctx) const {
    // Reduce terms \c e of the form
    //    elim_k A C e p[A,b] (intro_k_i A b u)
    environment const & env = ctx.env();
    inductive_env_ext const & ext = get_extension(env);
    expr const & elim_fn   = get_app_fn(e);
    if (!is_constant(elim_fn))
        return none_expr();
    auto it1 = ext.m_elim_info.find(const_name(elim_fn));
    if (!it1)
        return none_expr(); // it is not an eliminator
    buffer<expr> elim_args;
    get_app_args(e, elim_args);
    unsigned major_idx = it1->m_num_ACe + it1->m_num_indices;
    if (elim_args.size() < major_idx + 1)
        return none_expr(); // major premise is missing
    expr major = elim_args[major_idx];
    optional<expr> intro_app;
    inductive_env_ext::comp_rule const * it2 = nullptr;
    if (it1->m_K_target) {
        if (auto p = to_intro_when_K(it1, major, ctx)) {
            intro_app = p;
            it2       = ext.m_comp_rules.find(const_name(get_app_fn(*intro_app)));
        }
    }
    if (!intro_app) {
        intro_app         = ctx.whnf(major);
        it2               = is_intro_for(ext, const_name(elim_fn), *intro_app);
        if (!it2)
            return none_expr();
    }
    lean_assert(intro_app);
    lean_assert(it2);
    buffer<expr> intro_args;
    get_app_args(*intro_app, intro_args);
    // Check intro num_args
    if (intro_args.size() != it1->m_num_params + it2->m_num_bu)
        return none_expr();
    // Number of universe levels must match.
    if (length(const_levels(elim_fn)) != length(it1->m_level_names))
        return none_expr();
    buffer<expr> ACebu;
    for (unsigned i = 0; i < it1->m_num_ACe; i++)
        ACebu.push_back(elim_args[i]);
    for (unsigned i = 0; i < it2->m_num_bu; i++)
        ACebu.push_back(intro_args[it1->m_num_params + i]);
    std::reverse(ACebu.begin(), ACebu.end());
    expr r = instantiate_univ_params(it2->m_comp_rhs_body, it1->m_level_names, const_levels(elim_fn));
    r = instantiate(r, ACebu.size(), ACebu.data());
    if (elim_args.size() > major_idx + 1) {
        unsigned num_args = elim_args.size() - major_idx - 1;
        r = mk_app(r, num_args, elim_args.data() + major_idx + 1);
    }
    return some_expr(r);
}

bool inductive_normalizer_extension::is_recursor(environment const & env, name const & n) const {
    return static_cast<bool>(is_elim_rule(env, n));
}

bool inductive_normalizer_extension::is_builtin(environment const & env, name const & n) const {
    return is_inductive_decl(env, n) || is_elim_rule(env, n) || is_intro_rule(env, n);
}

template<typename Ctx>
optional<expr> is_elim_meta_app_core(Ctx & ctx, expr const & e) {
    inductive_env_ext const & ext = get_extension(ctx.env());
    expr const & elim_fn   = get_app_fn(e);
    if (!is_constant(elim_fn))
        return none_expr();
    auto it1 = ext.m_elim_info.find(const_name(elim_fn));
    if (!it1)
        return none_expr();
    buffer<expr> elim_args;
    get_app_args(e, elim_args);
    unsigned major_idx = it1->m_num_ACe + it1->m_num_indices;
    if (elim_args.size() < major_idx + 1)
        return none_expr();
    expr intro_app = ctx.whnf(elim_args[major_idx]);
    if (it1->m_K_target) {
        // TODO(Leo): make it more precise.  Remark: this piece of
        // code does not affect the correctness of the kernel, but the
        // effectiveness of the elaborator.
        return has_expr_metavar_strict(intro_app);
    } else {
        return ctx.is_stuck(intro_app);
    }
}

bool is_elim_meta_app(type_checker & tc, expr const & e) {
    return static_cast<bool>(is_elim_meta_app_core(tc, e));
}

// Return true if \c e is of the form (elim ... (?m ...))
optional<expr> inductive_normalizer_extension::is_stuck(expr const & e, abstract_type_context & ctx) const {
    return is_elim_meta_app_core(ctx, e);
}

optional<inductive_decl> is_inductive_decl(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_inductive_info.find(n))
        return optional<inductive_decl>(*it);
    else
        return optional<inductive_decl>();
}

optional<unsigned> get_num_indices(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(get_elim_name(n))) {
        return optional<unsigned>(it->m_num_indices);
    } else {
        return optional<unsigned>();
    }
}

optional<unsigned> get_num_minor_premises(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(get_elim_name(n))) {
        unsigned num_Cs = 1;
        return some(it->m_num_ACe - it->m_num_params - num_Cs);
    } else {
        return optional<unsigned>();
    }
}

optional<unsigned> get_num_intro_rules(environment const & env, name const & n) {
    if (auto decl = is_inductive_decl(env, n)) {
        return some(length(decl->m_intro_rules));
    } else {
        return optional<unsigned>();
    }
}

bool has_dep_elim(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(get_elim_name(n)))
        return it->m_dep_elim;
    else
        return false;
}

optional<name> is_intro_rule(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_intro_info.find(n))
        return optional<name>(*it);
    else
        return optional<name>();
}

optional<name> is_elim_rule(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(n))
        return optional<name>(it->m_inductive_name);
    else
        return optional<name>();
}

optional<unsigned> get_elim_major_idx(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(n))
        return optional<unsigned>(it->m_num_ACe + it->m_num_indices);
    else
        return optional<unsigned>();
}
}

void initialize_inductive_module() {
    inductive::g_ind_fresh           = new name("_ind_fresh");
    register_name_generator_prefix(*inductive::g_ind_fresh);
    inductive::g_inductive_extension = new name("inductive_extension");
    inductive::g_ext                 = new inductive::inductive_env_ext_reg();
}

void finalize_inductive_module() {
    delete inductive::g_ext;
    delete inductive::g_inductive_extension;
    delete inductive::g_ind_fresh;
}
}
