/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"

namespace lean {
static name * g_ind_fresh = nullptr;

/**\ brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I) {
    return I + name("rec");
}

class add_inductive_fn {
    environment            m_env;
    name_generator         m_ngen;
    local_ctx              m_lctx;
    level_param_names      m_lparams;
    unsigned               m_nparams;
    buffer<inductive_type> m_ind_types;
    buffer<unsigned>       m_nindices;
    level                  m_result_level;
    /* m_lparams ==> m_levels */
    levels                 m_levels;
    /* We track whether the resultant universe cannot be zero for any
       universe level instantiation */
    bool                   m_is_not_zero;
    /* A free variable for each parameter */
    buffer<expr>           m_params;
    /* A constant for each inductive type */
    buffer<expr>           m_ind_cnsts;

    level                  m_elim_level;
    bool                   m_K_target;

    struct rec_info {
        name         m_name;
        local_ctx    m_lctx;
        buffer<expr> m_Cs;       /* free variables for all motives */
        expr         m_C;        /* free variable for "main" motive */
        buffer<expr> m_minor;    /* minor premises */
        buffer<expr> m_indices;
        expr         m_major;    /* major premise */
    };

    /* We have an entry for each inductive datatype being declared,
       and for nested inductive datatypes. */
    buffer<rec_info>       m_rec_infos;

public:
    add_inductive_fn(environment const & env, inductive_decl const & decl):
        m_env(env), m_ngen(*g_ind_fresh), m_lparams(decl.get_lparams()) {
        if (!decl.get_nparams().is_small())
            throw kernel_exception(env, "invalid inductive datatype, number of parameters is too big");
        m_nparams = decl.get_nparams().get_small_value();
        to_buffer(decl.get_types(), m_ind_types);
    }

    void dump() {
        std::cout << "add_inductive_decl\n";
        for (inductive_type const & ind_type : m_ind_types) {
            std::cout << "ind>>   " << ind_type.get_name() << " : " << ind_type.get_type() << "\n";
            for (constructor const & c : ind_type.get_cnstrs()) {
                std::cout << ">>       " << constructor_name(c) << " : " << constructor_type(c) << "\n";
            }
        }
    }

    /**
       \brief Check whether the type of each datatype is well typed, and do not contain free variables or meta variables,
       all inductive datatypes have the same parameters, the number of parameters match the argument m_nparams,
       and the result universes are equivalent.

       This method also initializes the fields:
       - m_levels
       - m_result_level
       - m_nindices
       - m_ind_cnsts
       - m_params

       \remark The local context m_lctx contains the free variables in m_params. */
    void check_inductive_types() {
        m_levels   = param_names_to_levels(m_lparams);
        bool first = true;
        for (inductive_type const & ind_type : m_ind_types) {
            expr type = ind_type.get_type();
            check_no_metavar_no_fvar(m_env, ind_type.get_name(), type);
            type_checker(m_env).check(type, m_lparams);
            m_nindices.push_back(0);
            unsigned i = 0;
            while (is_pi(type)) {
                if (i < m_nparams) {
                    expr param = m_lctx.mk_local_decl(m_ngen, binding_name(type), binding_domain(type), binding_info(type));
                    m_params.push_back(param);
                    type = instantiate(binding_body(type), param);
                    i++;
                } else {
                    type = binding_body(type);
                    m_nindices.back()++;
                }
            }
            if (i != m_nparams)
                throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");

            type = type_checker(m_env, m_lctx).ensure_sort(type);

            if (first) {
                m_result_level = sort_level(type);
                m_is_not_zero  = is_not_zero(m_result_level);
            } else if (!is_equivalent(sort_level(type), m_result_level)) {
                throw kernel_exception(m_env, "mutually inductive types must live in the same universe");
            }

            m_ind_cnsts.push_back(mk_constant(ind_type.get_name(), m_levels));
            first = false;
        }

        lean_assert(length(m_levels) == length(m_lparams));
        lean_assert(m_nindices.size() == m_ind_types.size());
        lean_assert(m_ind_cnsts.size() == m_ind_types.size());
        lean_assert(m_params.size() == m_nparams);
    }

    /** \brief Add all datatype declarations to environment as axioms.

        We will update them later using `mk_inductive` when we know the exact number of
        recursors. */
    void declare_inductive_types_as_constants() {
        for (inductive_type const & ind_type : m_ind_types) {
            name const & n = ind_type.get_name();
            if (m_env.m_constants.find(n))
                throw already_declared_exception(m_env, n);
            m_env.m_constants.insert(n, constant_info(mk_axiom(n, m_lparams, ind_type.get_type())));
        }
    }

    /** \brief Return true if recursor can only map into Prop */
    bool elim_only_at_universe_zero() {
        if (m_is_not_zero) {
            /* For every universe parameter assignment, the resultant universe is not 0.
               So, it is not an inductive predicate */
            return false;
        }

        if (m_ind_types.size() > 1) {
            /* Mutually recursive inductive predicates only eliminate into Prop. */
            return true;
        }

        unsigned num_intros = length(m_ind_types[0].get_cnstrs());
        if (num_intros > 1) {
            /* We have more than one constructor, then recursor for inductive predicate
               can only eliminate intro Prop. */
            return true;
        }

        if (num_intros == 0) {
            /* empty inductive predicate (e.g., `false`) can eliminate into any universe */
            return false;
        }

        /* We have only one constructor, the final check is, the type of each argument
           that is not a parameter:
            1- It must live in Prop, *OR*
            2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
               We can justify 2 by observing that this information is not a *secret* it is part of the type.
               By eliminating to a non-proposition, we would not be revealing anything that is not already known. */
        constructor const & cnstr = head(m_ind_types[0].get_cnstrs());
        expr type  = constructor_type(cnstr);
        unsigned i = 0;
        buffer<expr> to_check; /* Arguments that we must check if occur in the result type */
        local_ctx lctx;
        while (is_pi(type)) {
            expr fvar = lctx.mk_local_decl(m_ngen, binding_name(type), binding_domain(type), binding_info(type));
            if (i >= m_nparams) {
                expr s = type_checker(m_env, lctx).ensure_type(binding_domain(type));
                if (!is_zero(sort_level(s))) {
                    /* Current argument is not in Prop (i.e., condition 1 failed).
                       We save it in to_check to be able to try condition 2 above. */
                    to_check.push_back(fvar);
                }
            }
            type = instantiate(binding_body(type), fvar);
            i++;
        }
        buffer<expr> result_args;
        get_app_args(type, result_args);
        /* Check condition 2: every argument in to_check must occur in result_args */
        for (expr const & arg : to_check) {
            if (std::find(result_args.begin(), result_args.end(), arg) == result_args.end())
                return true; /* Condition 2 failed */
        }
        return false;
    }

    /** \brief Initialize m_elim_level. */
    void init_elim_level() {
        if (elim_only_at_universe_zero()) {
            m_elim_level = mk_level_zero();
        } else {
            name u("u");
            int i = 1;
            while (std::find(m_lparams.begin(), m_lparams.end(), u) != m_lparams.end()) {
                u = name("u").append_after(i);
                i++;
            }
            m_elim_level = mk_univ_param(u);
        }
        std::cout << ">> elim_level: " << m_elim_level << "\n";
    }

    void init_K_target() {
        /* A declaration is target for K-like reduction when
           it has one intro, the intro has 0 arguments, and it is an inductive predicate.
           In the following for-loop we check if the intro rule has 0 fields. */
        m_K_target =
            m_ind_types.size() == 1 &&              /* It is not a mutual declaration (for simplicity, we don't gain anything by supporting K in mutual declarations. */
            is_zero(m_result_level) &&              /* It is an inductive predicate. */
            length(m_ind_types[0].get_cnstrs()) == 1; /* Inductive datatype has only one constructor. */
        if (!m_K_target)
            return;
        expr it = constructor_type(head(m_ind_types[0].get_cnstrs()));
        unsigned i = 0;
        while (is_pi(it)) {
            if (i < m_nparams) {
                it = binding_body(it);
            } else {
                /* See comment above */
                m_K_target = false;
                break;
            }
            i++;
        }
    }

    void check_constructor(constructor const & cnstr, unsigned /* idx */) {
        check_no_metavar_no_fvar(m_env, constructor_name(cnstr), constructor_type(cnstr));
        type_checker(m_env).check(constructor_type(cnstr), m_lparams);
    }

    void check_constructors() {
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                check_constructor(cnstr, idx);
            }
        }
    }

    environment operator()() {
        dump();
        check_inductive_types();
        declare_inductive_types_as_constants();
        init_elim_level();
        init_K_target();

        return m_env;
    }
};

environment environment::add_inductive(declaration const & d) const {
    return add_inductive_fn(*this, inductive_decl(d))();
}

void initialize_inductive() {
    g_ind_fresh = new name("_ind_fresh");
}

void finalize_inductive() {
    delete g_ind_fresh;
}
}
