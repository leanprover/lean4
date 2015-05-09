/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "util/sstream.h"
#include "util/list_fn.h"
#include "util/rb_map.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "kernel/find_fn.h"

/*
   The implementation is based on the paper: "Inductive Families", Peter Dybjer, 1997
   The main differences are:
      - Support for Prop (when environment is marked as impredicative)
      - Universe levels

   The support for Prop is based on the paper: "Inductive Definitions in the System Coq: Rules and Properties",
   Christine Paulin-Mohring.

   Given a sequence of universe levels parameters (m_level_names), each datatype decls have the form
         I_k : (A :: \sigma) (a :: \alpha[A]), Type.{l_k}
               I_k is the name of the k-th inductive datatype
               A   is the sequence of global parameters (it must have size m_num_params)
               a   is the sequence of indices

         remark: all mutually recursive inductive datatype decls must use the same sequence of global parameters.

   Each inductive declaration has a sequence of introduction rules of the form
         intro_k_i : (A :: \sigma) (b :: \beta[A]) (u :: \gama[A, b]), I_k A p[A, b]
               A is the sequence of global parameters (it must have size m_num_params)
               b is the sequence of non-recursive arguments (i.e., they do not include any I_k)
               u is the sequence of recursive arguments (they contain positive occurrences of I_j, j is not necessarily equal to k)
         each u_i, in the sequence u, is of the form
               x :: \Epsilon[A, b], I_j A p_i[A, b, x]

         Again, all introduction rules must have the same sequence of global parameters

   The universe levels of arguments b and u must be smaller than or equal to l_k in I_k.

   When the environment is marked as impredicative, then l_k must be 0 (Prop) or must be different from zero for
   any instantiation of the universe level parameters (and global level parameters).

   This module produces an eliminator/recursor for each inductive datatype I_k, it has the form.
   The eliminator has an extra univese level parameter when
          1- Type.{0} is not impredicative in the given environment
          2- l_k is never zero (for any universe level assignment)
          3- There is only one introduction rule
   Let l' be this extra universe level, in the following rules, and 0 if none of the conditions above hold.

        elim_k : (A :: \sigma)
                 (C :: (a :: \alpha[A]) (c : I_k A a), Type.{l'})
                 (e :: \epsilon[A])
                 (a :: \alpha[A])
                 (n :: I_k A a),
               C_k a n

          A is the sequence of global parameters
          C is the sequence of type formers. The size of the sequence is equal to the number of inductive datatype beging declared.
             We say C_k is the type former for I_k
          e is the sequence of minor premises. The size of the sequence is equal to the sum of the length of all introduction rules.
          a is the sequence of indices, it is equal to sequence occurring in I_k
          n is the major premise

    The minor premise e_i_j : \epsilon_i_j[A] in (e:: \epsilon[A]) corresponds to the j-th introduction rule in the inductive
    datatype I_i.

       \epsilon_i_j[A] : (b :: \beta[A]) (u :: \gama[A, b]) (v :: \delta[A, b]), C_i p[A, b] intro_i_j A b u

           b and u are the corresponding arguments in intro_i_j. \delta[A, b] has the same length of \gama[A, b],
           and \delta_i[A, b] is
                       (x :: \Epsilon_i[A, b]), C_j p_i[A, b, x] (u_i x)
           C_j corresponds to the I_j used in u_i

     When the environment is impredicative and l_k is zero, then we use nondependent elimination, and we omit
     the argument c in C, and v in the minor premises. That is, C becomes
            (C :: (a :: \alpha[A]), Type.{l'})
     and \epsilon_i_j[A]
            \epsilon_i_j[A] : (b :: \beta[A]) (u :: \gama[A, b]), C_i p[A, b]


     Finally, this module also generate computational rules for the extended normalizer. Actually, we only generate
     the right hand side for the rules. They have the form

        Fun (A, C, e, b, u), elim_k A C e p[A,b] (intro_k_i A b u) ==>
               Fun (A, C, e, b, u), (e_k_i b u v)
*/
namespace lean {
namespace inductive {
static name * g_tmp_prefix = nullptr;
static name * g_inductive_extension = nullptr;

/** \brief Environment extension used to store the computational rules associated with inductive datatype declarations. */
struct inductive_env_ext : public environment_extension {
    struct elim_info {
        name              m_inductive_name; // name of the inductive datatype associated with eliminator
        level_param_names m_level_names; // level parameter names used in computational rule
        unsigned          m_num_params;  // number of global parameters A
        unsigned          m_num_ACe;     // sum of number of global parameters A, type formers C, and minor preimises e.
        unsigned          m_num_indices; // number of inductive datatype indices
        /** \brief We support K-like reduction when the inductive datatype is in Type.{0} (aka Prop), proof irrelevance
            is enabled, it has only one introduction rule, the introduction rule has "0 arguments".
            Example: equality defined as

            inductive eq {A : Type} (a : A) : A -> Prop :=
            refl : eq a a

            satisfies these requirements when proof irrelevance is enabled.
            Another example is heterogeneous equality.
        */
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
    name_map<inductive_decls>       m_inductive_info;

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

    void add_inductive_info(level_param_names const & ps, unsigned num_params, list<inductive_decl> const & ds) {
        inductive_decls decls(ps, num_params, ds);
        for (auto const & d : ds)
            m_inductive_info.insert(inductive_decl_name(d), decls);
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

/** \brief Helper functional object for processing inductive datatype declarations. */
struct add_inductive_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    environment          m_env;
    level_param_names    m_level_names;  // universe level parameters
    unsigned             m_num_params;
    list<inductive_decl> m_decls;
    // when kernel sets Type.{0} as impredicative, then
    // we track whether the resultant universe cannot be zero for any
    // universe level instantiation
    bool                 m_is_not_zero;
    unsigned             m_decls_sz;     // length(m_decls)
    list<level>          m_levels;       // m_level_names ==> m_levels
    name_generator       m_ngen;
    type_checker_ptr     m_tc;

    level                m_elim_level;   // extra universe level for eliminator.
    bool                 m_dep_elim;     // true if using dependent elimination

    buffer<expr>         m_param_consts; // local constants used to represent global parameters
    buffer<level>        m_it_levels;    // the levels for each inductive datatype in m_decls
    buffer<expr>         m_it_consts;    // the constants for each inductive datatype in m_decls
    buffer<unsigned>     m_it_num_args;  // total number of arguments (params + indices) for each inductive datatype in m_decls

    struct elim_info {
        expr             m_C;              // type former constant
        buffer<expr>     m_indices;        // local constant for each index
        expr             m_major_premise;  // major premise for each inductive decl
        buffer<expr>     m_minor_premises; // minor premise for each introduction rule
        bool             m_K_target;
        elim_info():m_K_target(false) {}
    };
    buffer<elim_info>    m_elim_info; // for each datatype being declared

    add_inductive_fn(environment                  env,
                     level_param_names const &    level_params,
                     unsigned                     num_params,
                     list<inductive_decl> const & decls):
        m_env(env), m_level_names(level_params), m_num_params(num_params), m_decls(decls),
        m_ngen(*g_tmp_prefix), m_tc(new type_checker(m_env)) {
        m_is_not_zero = false;
        m_decls_sz    = length(m_decls);
        m_levels      = param_names_to_levels(level_params);
    }

    /** \brief Return the number of inductive datatypes being defined. */
    unsigned get_num_its() const { return m_decls_sz; }

    /** \brief Make sure the latest environment is being used by m_tc. */
    void updt_type_checker() {
        m_tc.reset(new type_checker(m_env));
    }

    type_checker & tc() { return *(m_tc.get()); }
    bool is_def_eq(expr const & t, expr const & s) { return tc().is_def_eq(t, s).first; }
    expr whnf(expr const & e) { return tc().whnf(e).first; }
    expr ensure_type(expr const & e) { return tc().ensure_type(e).first; }

    /** \brief Return a fresh name. */
    name mk_fresh_name() { return m_ngen.next(); }

    /** \brief Create a local constant for the given binding. */
    expr mk_local_for(expr const & b) { return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b)); }

    /** \brief Return type of the i-th global parameter. */
    expr get_param_type(unsigned i) { return mlocal_type(m_param_consts[i]); }

     /**
       \brief Check if the type of datatypes is well typed, all inductive datatypes have the same parameters,
       and the number of parameters match the argument num_params.

       This method also populates the fields m_param_consts, m_it_levels, m_it_consts.
    */
    void check_inductive_types() {
        bool first   = true;
        for (auto d : m_decls) {
            expr t = inductive_decl_type(d);
            tc().check(t, m_level_names);
            unsigned i  = 0;
            m_it_num_args.push_back(0);
            while (is_pi(t)) {
                if (i < m_num_params) {
                    if (first) {
                        expr l = mk_local_for(t);
                        m_param_consts.push_back(l);
                        t = instantiate(binding_body(t), l);
                    } else {
                        if (!is_def_eq(binding_domain(t), get_param_type(i)))
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
            t = tc().ensure_sort(t).first;
            if (m_env.impredicative()) {
                // If the environment is impredicative, we track whether the resultant universe
                // is never zero (under any parameter assignment).
                // TODO(Leo): when the resultant universe may be 0 and not zero depending on parameter assignment,
                // we may generate two recursors: one when it is 0, and another one when it is not.
                if (first) {
                    m_is_not_zero = is_not_zero(sort_level(t));
                } else {
                    if (is_not_zero(sort_level(t)) != m_is_not_zero)
                        throw kernel_exception(m_env,
                                               "for impredicative environments, if one datatype is in Prop, "
                                               "then all of them must be in Prop");
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
            m_env = m_env.add(check(m_env, mk_constant_assumption(inductive_decl_name(d), m_level_names, inductive_decl_type(d))));
        }
        inductive_env_ext ext(get_extension(m_env));
        ext.add_inductive_info(m_level_names, m_num_params, m_decls);
        m_env = update(m_env, ext);
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
        if (!is_def_eq(I, m_it_consts[d_idx]) || args.size() != m_it_num_args[d_idx])
            return false;
        for (unsigned i = 0; i < m_num_params; i++) {
            if (m_param_consts[i] != args[i])
                return false;
        }
        return true;
    }

    /** \brief Return some(i) iff \c t is a valid occurrence of the i-th datatype being defined. */
    optional<unsigned> is_valid_it_app(expr const & t) {
        for (unsigned i = 0; i < get_num_its(); i++) {
            if (is_valid_it_app(t, i))
                return optional<unsigned>(i);
        }
        return optional<unsigned>();
    }

    /** \brief Return true iff \c e is one of the inductive datatype being declared. */
    bool is_it_occ(expr const & e) {
        return
            is_constant(e) &&
            std::any_of(m_it_consts.begin(), m_it_consts.end(), [&](expr const & c) { return const_name(e) == const_name(c); });
    }

    /** \brief Return true if \c t does not contain any occurrence of a datatype being declared. */
    bool has_it_occ(expr const & t) {
        return (bool)find(t, [&](expr const & e, unsigned) { return is_it_occ(e); }); // NOLINT
    }

    /**
        \brief Return some(d_idx) iff \c t is a recursive argument, \c d_idx is the index of the recursive inductive datatype.
        Return none otherwise.
    */
    optional<unsigned> is_rec_argument(expr t) {
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

    /**
       \brief Check the intro_rule \c ir of the given inductive decl. \c d_idx is the position of \c d in m_decls.

       \see check_intro_rules
    */
    void check_intro_rule(unsigned d_idx, intro_rule const & ir) {
        expr t = intro_rule_type(ir);
        name n = intro_rule_name(ir);
        tc().check(t, m_level_names);
        unsigned i     = 0;
        bool found_rec = false;
        while (is_pi(t)) {
            if (i < m_num_params) {
                if (!is_def_eq(binding_domain(t), get_param_type(i)))
                    throw kernel_exception(m_env, sstream() << "arg #" << (i + 1) << " of '" << n << "' "
                                           << "does not match inductive datatypes parameters'");
                t = instantiate(binding_body(t), m_param_consts[i]);
            } else {
                expr s = ensure_type(binding_domain(t));
                // the sort is ok IF
                //   1- its level is <= inductive datatype level, OR
                //   2- m_env is impredicative and inductive datatype is at level 0
                if (!(is_geq(m_it_levels[d_idx], sort_level(s)) || (is_zero(m_it_levels[d_idx]) && m_env.impredicative())))
                    throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << (i + 1) << ") "
                                           << "of '" << n << "' is too big for the corresponding inductive datatype");
                check_positivity(binding_domain(t), n, i);
                bool is_rec = (bool)is_rec_argument(binding_domain(t)); // NOLINT
                if (found_rec && !is_rec)
                    throw kernel_exception(m_env, sstream() << "arg #" << (i + 1) << " of '" << n << "' "
                                           << "is not recursive, but it occurs after recursive arguments");
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
                check_intro_rule(i, ir);
            i++;
        }
    }

    /** \brief Add all introduction rules (aka constructors) to environment. */
    void declare_intro_rules() {
        inductive_env_ext ext(get_extension(m_env));
        for (auto d : m_decls) {
            for (auto ir : inductive_decl_intros(d)) {
                m_env = m_env.add(check(m_env, mk_constant_assumption(intro_rule_name(ir), m_level_names, intro_rule_type(ir))));
                ext.add_intro_info(intro_rule_name(ir), inductive_decl_name(d));
            }
        }
        m_env = update(m_env, ext);
        updt_type_checker();
    }

    /** \brief Return true if type formers C in the recursors can only map to Type.{0} */
    bool elim_only_at_universe_zero() {
        if (!m_env.impredicative() || m_is_not_zero) {
            // If Type.{0} is not impredicative or the resultant inductive datatype is not in Type.{0},
            // then the recursor may return Type.{l} where l is a universe level parameter.
            return false;
        }
        if (get_num_its() > 1)
            return true; // we don't consider mutually recursive datatypes for propositions
        unsigned num_intros = length(inductive_decl_intros(head(m_decls)));
        if (num_intros > 1) {
            // If we have more than one introduction rule, then yes, the type formers can only
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
        auto ir    = head(inductive_decl_intros(head(m_decls)));
        expr t     = intro_rule_type(ir);
        unsigned i = 0;
        buffer<expr> to_check; // arguments that we must check if occur in the result type
        while (is_pi(t)) {
            expr local = mk_local_for(t);
            if (i >= m_num_params) {
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
            while (std::find(m_level_names.begin(), m_level_names.end(), l) != m_level_names.end()) {
                l = name("l").append_after(i);
                i++;
            }
            m_elim_level = mk_param_univ(l);
        }
    }

    /** \brief Initialize m_dep_elim flag. */
    void set_dep_elim() {
        if (m_env.impredicative() && m_env.prop_proof_irrel() && is_zero(m_it_levels[0]))
            m_dep_elim = false;
        else
            m_dep_elim = true;
    }

    /**
        \brief Given t of the form (I As is) where I is one of the inductive datatypes being defined,
        As are the global parameters, and is the actual indices provided to it.
        Return the index of I, and store is in the argument \c indices.
    */
    unsigned get_I_indices(expr const & t, buffer<expr> & indices) {
        optional<unsigned> r = is_valid_it_app(t);
        lean_assert(r);
        buffer<expr> all_args;
        get_app_args(t, all_args);
        for (unsigned i = m_num_params; i < all_args.size(); i++)
            indices.push_back(all_args[i]);
        return *r;
    }

    /** \brief Populate m_elim_info. */
    void mk_elim_info() {
        unsigned d_idx = 0;
        // First, populate the fields, m_C, m_indices, m_major_premise
        for (auto d : m_decls) {
            elim_info info;
            expr t     = inductive_decl_type(d);
            unsigned i = 0;
            while (is_pi(t)) {
                if (i < m_num_params) {
                    t = instantiate(binding_body(t), m_param_consts[i]);
                } else {
                    expr c = mk_local_for(t);
                    info.m_indices.push_back(c);
                    t = instantiate(binding_body(t), c);
                }
                i++;
            }
            info.m_major_premise = mk_local(mk_fresh_name(), "n",
                                            mk_app(mk_app(m_it_consts[d_idx], m_param_consts), info.m_indices), binder_info());
            expr C_ty = mk_sort(m_elim_level);
            if (m_dep_elim)
                C_ty = Pi(info.m_major_premise, C_ty);
            C_ty = Pi(info.m_indices, C_ty);
            name C_name("C");
            if (get_num_its() > 1)
                C_name = name(C_name).append_after(d_idx+1);
            info.m_C = mk_local(mk_fresh_name(), C_name, C_ty, binder_info());
            m_elim_info.push_back(info);
            d_idx++;
        }
        // First, populate the field m_minor_premises
        unsigned minor_idx = 1;
        d_idx = 0;
        for (auto d : m_decls) {
            // A declaration is target for K-like reduction when
            // it has one intro, the intro has 0 arguments, proof irrelevance is enabled,
            // and it is a proposition.
            // In the following for-loop we check if the intro rule
            // has 0 arguments.
            bool is_K_target =
                m_env.prop_proof_irrel() &&  // Proof irrelevance is enabled
                is_zero(m_it_levels[d_idx]) &&   // It a Prop
                length(inductive_decl_intros(d)) == 1; // datatype has only one intro rule
            for (auto ir : inductive_decl_intros(d)) {
                buffer<expr> b; // nonrec args
                buffer<expr> u; // rec args
                buffer<expr> v; // inductive args
                expr t     = intro_rule_type(ir);
                unsigned i = 0;
                while (is_pi(t)) {
                    if (i < m_num_params) {
                        t = instantiate(binding_body(t), m_param_consts[i]);
                    } else {
                        is_K_target = false; // See comment before for-loop.
                        expr l = mk_local_for(t);
                        if (!is_rec_argument(binding_domain(t)))
                            b.push_back(l);
                        else
                            u.push_back(l);
                        t = instantiate(binding_body(t), l);
                    }
                    i++;
                }
                buffer<expr> it_indices;
                unsigned it_idx = get_I_indices(t, it_indices);
                expr C_app      = mk_app(m_elim_info[it_idx].m_C, it_indices);
                if (m_dep_elim) {
                    expr intro_app  = mk_app(mk_app(mk_app(mk_constant(intro_rule_name(ir), m_levels), m_param_consts), b), u);
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
                    unsigned it_idx = get_I_indices(u_i_ty, it_indices);
                    expr C_app  = mk_app(m_elim_info[it_idx].m_C, it_indices);
                    if (m_dep_elim) {
                        expr u_app  = mk_app(u_i, xs);
                        C_app = mk_app(C_app, u_app);
                    }
                    expr v_i_ty = Pi(xs, C_app);
                    expr v_i    = mk_local(mk_fresh_name(), name("v").append_after(i), v_i_ty, binder_info());
                    v.push_back(v_i);
                }
                expr minor_ty = Pi(b, Pi(u, Pi(v, C_app)));
                expr minor = mk_local(mk_fresh_name(), name("e").append_after(minor_idx), minor_ty, binder_info());
                m_elim_info[d_idx].m_minor_premises.push_back(minor);
                minor_idx++;
            }
            m_elim_info[d_idx].m_K_target = is_K_target;
            d_idx++;
        }
    }

    /** \brief Return the name of the eliminator/recursor for \c d. */
    name get_elim_name(inductive_decl const & d) { return ::lean::inductive::get_elim_name(inductive_decl_name(d)); }

    name get_elim_name(unsigned d_idx) { return get_elim_name(get_ith(m_decls, d_idx)); }

    /** \brief Return the level parameter names for the eliminator. */
    level_param_names get_elim_level_param_names() {
        if (is_param(m_elim_level))
            return level_param_names(param_id(m_elim_level), m_level_names);
        else
            return m_level_names;
    }

    /** \brief Return the levels for the eliminator application. */
    levels get_elim_level_params() {
        if (is_param(m_elim_level))
            return levels(m_elim_level, m_levels);
        else
            return m_levels;
    }

    /** \brief Declare elimination rule. */
    void declare_elim_rule(inductive_decl const & d, unsigned d_idx) {
        elim_info const & info = m_elim_info[d_idx];
        expr C_app   = mk_app(info.m_C, info.m_indices);
        if (m_dep_elim)
            C_app = mk_app(C_app, info.m_major_premise);
        expr elim_ty = Pi(info.m_major_premise, C_app);
        elim_ty   = Pi(info.m_indices, elim_ty);
        // abstract all introduction rules
        unsigned i = get_num_its();
        while (i > 0) {
            --i;
            unsigned j = m_elim_info[i].m_minor_premises.size();
            while (j > 0) {
                --j;
                elim_ty = Pi(m_elim_info[i].m_minor_premises[j], elim_ty);
            }
        }
        // abstract all type formers
        i = get_num_its();
        while (i > 0) {
            --i;
            elim_ty = Pi(m_elim_info[i].m_C, elim_ty);
        }
        elim_ty   = Pi(m_param_consts, elim_ty);
        elim_ty   = infer_implicit(elim_ty, true /* strict */);
        m_env = m_env.add(check(m_env, mk_constant_assumption(get_elim_name(d), get_elim_level_param_names(), elim_ty)));
    }

    /** \brief Declare the eliminator/recursor for each datatype. */
    void declare_elim_rules() {
        set_dep_elim();
        mk_elim_level();
        mk_elim_info();
        unsigned i = 0;
        for (auto d : m_decls) {
            declare_elim_rule(d, i);
            i++;
        }
        updt_type_checker();
    }

    /** \brief Store all type formers in \c Cs */
    void collect_Cs(buffer<expr> & Cs) {
        for (unsigned i = 0; i < get_num_its(); i++)
            Cs.push_back(m_elim_info[i].m_C);
    }

    /** \brief Store all minor premises in \c es. */
    void collect_minor_premises(buffer<expr> & es) {
        for (unsigned i = 0; i < get_num_its(); i++)
            es.append(m_elim_info[i].m_minor_premises);
    }

    /** \brief Return the number of indices of the i-th datatype. */
    unsigned get_num_indices(unsigned i) { return m_elim_info[i].m_indices.size(); }

    /** \brief Return true iff it is a target of a K-like reduction */
    bool is_K_target(unsigned i) { return m_elim_info[i].m_K_target; }

    /** \brief Create computional rules RHS. They are used by the normalizer extension. */
    void mk_comp_rules_rhs() {
        unsigned d_idx  = 0;
        unsigned minor_idx = 0;
        buffer<expr> C; collect_Cs(C);
        buffer<expr> e; collect_minor_premises(e);
        levels ls = get_elim_level_params();
        inductive_env_ext ext(get_extension(m_env));
        for (auto d : m_decls) {
            ext.add_elim(get_elim_name(d), inductive_decl_name(d), get_elim_level_param_names(), m_num_params,
                         m_num_params + C.size() + e.size(), get_num_indices(d_idx), is_K_target(d_idx), m_dep_elim);
            for (auto ir : inductive_decl_intros(d)) {
                buffer<expr> b;
                buffer<expr> u;
                expr t = intro_rule_type(ir);
                unsigned i = 0;
                while (is_pi(t)) {
                    if (i < m_num_params) {
                        t = instantiate(binding_body(t), m_param_consts[i]);
                    } else {
                        expr l = mk_local_for(t);
                        if (!is_rec_argument(binding_domain(t)))
                            b.push_back(l);
                        else
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
                    unsigned it_idx = get_I_indices(u_i_ty, it_indices);
                    expr elim_app = mk_constant(get_elim_name(it_idx), ls);
                    elim_app = mk_app(mk_app(mk_app(mk_app(mk_app(elim_app, m_param_consts), C), e), it_indices), mk_app(u_i, xs));
                    v.push_back(Fun(xs, elim_app));
                }
                expr e_app = mk_app(mk_app(mk_app(e[minor_idx], b), u), v);
                expr comp_rhs   = Fun(m_param_consts, Fun(C, Fun(e, Fun(b, Fun(u, e_app)))));
                tc().check(comp_rhs, get_elim_level_param_names());
                ext.add_comp_rhs(intro_rule_name(ir), get_elim_name(d_idx), b.size() + u.size(), comp_rhs);
                minor_idx++;
            }
            d_idx++;
        }
        m_env = update(m_env, ext);
    }

    environment operator()() {
        if (!m_env.norm_ext().supports(*g_inductive_extension))
            throw kernel_exception(m_env, "environment does not support inductive datatypes");
        if (get_num_its() == 0)
            throw kernel_exception(m_env, "at least one inductive datatype declaration expected");
        check_inductive_types();
        declare_inductive_types();
        check_intro_rules();
        declare_intro_rules();
        declare_elim_rules();
        mk_comp_rules_rhs();
        return m_env;
    }
};

environment add_inductive(environment                  env,
                          level_param_names const &    level_params,
                          unsigned                     num_params,
                          list<inductive_decl> const & decls) {
    return add_inductive_fn(env, level_params, num_params, decls)();
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
    if (inductive_decls const * it = ext.m_inductive_info.find(d_name)) {
        list<inductive_decl> const & decls = std::get<2>(*it);
        for (auto const & decl : decls) {
            if (inductive_decl_name(decl) != d_name)
                continue;
            auto intros = inductive_decl_intros(decl);
            if (intros)
                return optional<name>(intro_rule_name(head(intros)));
        }
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
static optional<pair<expr, constraint_seq>> to_intro_when_K(inductive_env_ext::elim_info const * it,
                                                            expr const & e, extension_context & ctx) {
    lean_assert(it->m_K_target);
    environment const & env = ctx.env();
    constraint_seq cs;
    expr app_type    = ctx.whnf(ctx.infer_type(e, cs), cs);
    if (has_expr_metavar(app_type))
        return none_ecs();
    expr const & app_type_I = get_app_fn(app_type);
    if (!is_constant(app_type_I) || const_name(app_type_I) != it->m_inductive_name)
        return none_ecs(); // type incorrect
    auto new_intro_app = mk_nullary_intro(env, app_type, it->m_num_params);
    if (!new_intro_app)
        return none_ecs();
    expr new_type    = ctx.infer_type(*new_intro_app, cs);
    if (has_expr_metavar(new_type))
        return none_ecs();
    simple_delayed_justification jst([=]() {
            return mk_justification("elim/intro global parameters must match", some_expr(e));
        });
    if (!ctx.is_def_eq(app_type, new_type, jst, cs))
        return none_ecs();
    return some_ecs(*new_intro_app, cs);
}

auto inductive_normalizer_extension::operator()(expr const & e, extension_context & ctx) const
    -> optional<pair<expr, constraint_seq>> {
    // Reduce terms \c e of the form
    //    elim_k A C e p[A,b] (intro_k_i A b u)
    environment const & env = ctx.env();
    inductive_env_ext const & ext = get_extension(env);
    expr const & elim_fn   = get_app_fn(e);
    if (!is_constant(elim_fn))
        return none_ecs();
    auto it1 = ext.m_elim_info.find(const_name(elim_fn));
    if (!it1)
        return none_ecs(); // it is not an eliminator
    buffer<expr> elim_args;
    get_app_args(e, elim_args);
    unsigned major_idx = it1->m_num_ACe + it1->m_num_indices;
    if (elim_args.size() < major_idx + 1)
        return none_ecs(); // major premise is missing
    expr major = elim_args[major_idx];
    optional<expr> intro_app;
    constraint_seq cs;
    inductive_env_ext::comp_rule const * it2 = nullptr;
    if (it1->m_K_target) {
        if (auto p = to_intro_when_K(it1, major, ctx)) {
            intro_app = p->first;
            cs        = p->second;
            it2       = ext.m_comp_rules.find(const_name(get_app_fn(*intro_app)));
        }
    }
    if (!intro_app) {
        auto intro_app_cs = ctx.whnf(major);
        intro_app         = intro_app_cs.first;
        cs                = intro_app_cs.second;
        it2               = is_intro_for(ext, const_name(elim_fn), *intro_app);
        if (!it2)
            return none_ecs();
    }
    lean_assert(intro_app);
    lean_assert(it2);
    buffer<expr> intro_args;
    get_app_args(*intro_app, intro_args);
    // Check intro num_args
    if (intro_args.size() != it1->m_num_params + it2->m_num_bu)
        return none_ecs();
    // Number of universe levels must match.
    if (length(const_levels(elim_fn)) != length(it1->m_level_names))
        return none_ecs();
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
    return some_ecs(r, cs);
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
    expr intro_app = ctx.whnf(elim_args[major_idx]).first;
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
optional<expr> inductive_normalizer_extension::is_stuck(expr const & e, extension_context & ctx) const {
    return is_elim_meta_app_core(ctx, e);
}

optional<inductive_decls> is_inductive_decl(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_inductive_info.find(n))
        return optional<inductive_decls>(*it);
    else
        return optional<inductive_decls>();
}

optional<unsigned> get_num_indices(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(get_elim_name(n))) {
        return optional<unsigned>(it->m_num_indices);
    } else {
        return optional<unsigned>();
    }
}

optional<unsigned> get_num_type_formers(environment const & env, name const & n) {
    if (auto decls = is_inductive_decl(env, n)) {
        return some(length(std::get<2>(*decls)));
    } else {
        return optional<unsigned>();
    }
}

optional<unsigned> get_num_minor_premises(environment const & env, name const & n) {
    inductive_env_ext const & ext = get_extension(env);
    if (auto it = ext.m_elim_info.find(get_elim_name(n))) {
        unsigned num_Cs = *get_num_type_formers(env, n);
        return some(it->m_num_ACe - it->m_num_params - num_Cs);
    } else {
        return optional<unsigned>();
    }
}

optional<unsigned> get_num_intro_rules(environment const & env, name const & n) {
    if (auto decls = is_inductive_decl(env, n)) {
        for (auto const & decl : std::get<2>(*decls)) {
            if (inductive_decl_name(decl) == n)
                return some(length(inductive_decl_intros(decl)));
        }
        lean_unreachable();
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
    inductive::g_tmp_prefix          = new name(name::mk_internal_unique_name());
    inductive::g_inductive_extension = new name("inductive_extension");
    inductive::g_ext                 = new inductive::inductive_env_ext_reg();
}

void finalize_inductive_module() {
    delete inductive::g_ext;
    delete inductive::g_inductive_extension;
    delete inductive::g_tmp_prefix;
}
}
