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

class add_inductive_fn {
    environment            m_env;
    name_generator         m_ngen;
    local_ctx              m_lctx;
    level_param_names      m_level_params;
    unsigned               m_num_params;
    buffer<inductive_decl> m_decls;
    buffer<unsigned>       m_num_indices;
    level                  m_result_level;
    /* m_level_params ==> m_levels */
    levels                 m_levels;
    /* We track whether the resultant universe cannot be zero for any
       universe level instantiation */
    bool                   m_is_not_zero;
    /* A free variable for each parameter */
    buffer<expr>           m_params;
    /* A constant for each inductive type */
    buffer<expr>           m_decl_consts;
public:
    add_inductive_fn(environment const & env, inductive_decls const & decls):
        m_env(env), m_ngen(*g_ind_fresh), m_level_params(decls.m_level_params),
        m_num_params(decls.m_num_params) {
        to_buffer(decls.m_decls, m_decls);
    }

    void dump() {
        std::cout << "add_inductive_decls\n";
        for (inductive_decl const & d : m_decls) {
            std::cout << "ind>>   " << d.m_name << " : " << d.m_type << "\n";
            for (constructor const & c : d.m_constructors) {
                std::cout << ">>       " << c.m_name << " : " << c.m_type << "\n";
            }
        }
    }

    /**
       \brief Check whether the type of each datatype is well typed, and do not contain free variables or meta variables,
       all inductive datatypes have the same parameters, the number of parameters match the argument m_num_params,
       and the result universes are equivalent.

       This method also initializes the fields:
       - m_levels
       - m_result_level
       - m_num_indices
       - m_decl_consts
       - m_params

       \remark The local context m_lctx contains the free variables in m_params. */
    void check_inductive_types() {
        m_levels   = param_names_to_levels(m_level_params);
        bool first = true;
        for (inductive_decl const & decl : m_decls) {
            expr type = decl.m_type;
            check_no_metavar_no_fvar(m_env, decl.m_name, type);
            type_checker(m_env).check(type, m_level_params);
            m_num_indices.push_back(0);
            unsigned i = 0;
            while (is_pi(type)) {
                if (i < m_num_params) {
                    expr param = m_lctx.mk_local_decl(m_ngen, binding_name(type), binding_domain(type), binding_info(type));
                    m_params.push_back(param);
                    type = instantiate(binding_body(type), param);
                    i++;
                } else {
                    type = binding_body(type);
                    m_num_indices.back()++;
                }
            }
            if (i != m_num_params)
                throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");

            type = type_checker(m_env, m_lctx).ensure_sort(type);

            if (first) {
                m_result_level = sort_level(type);
                m_is_not_zero  = is_not_zero(m_result_level);
            } else if (!is_equivalent(sort_level(type), m_result_level)) {
                throw kernel_exception(m_env, "mutually inductive types must live in the same universe");
            }

            m_decl_consts.push_back(mk_constant(decl.m_name, m_levels));
            first = false;
        }

        lean_assert(length(m_levels) == length(m_level_params));
        lean_assert(m_num_indices.size() == m_decls.size());
        lean_assert(m_decl_consts.size() == m_decls.size());
        lean_assert(m_params.size() == m_num_params);
    }

    /** \brief Add all datatype declarations to environment. */
    void declare_inductive_types() {
        for (inductive_decl const & decl : m_decls) {
            /* TODO(Leo): we should not use constant_assumption, but a new kind of declaration. */
            m_env = m_env.add(check(m_env, mk_constant_assumption(decl.m_name, m_level_params, decl.m_type)));
        }
    }

    void check_constructor(constructor const & cnstr, unsigned /* decl_idx */) {
        check_no_metavar_no_fvar(m_env, cnstr.m_name, cnstr.m_type);
        type_checker(m_env).check(cnstr.m_type, m_level_params);
    }

    void check_constructors() {
        for (unsigned decl_idx = 0; decl_idx < m_decls.size(); decl_idx++) {
            inductive_decl const & decl = m_decls[decl_idx];
            for (constructor const & cnstr : decl.m_constructors) {
                check_constructor(cnstr, decl_idx);
            }
        }
    }

    environment operator()() {
        dump();
        check_inductive_types();
        declare_inductive_types();
        return m_env;
    }
};

environment environment::add_inductive_decls(inductive_decls const & decls) const {
    return add_inductive_fn(*this, decls)();
}

void initialize_inductive() {
    g_ind_fresh = new name("_ind_fresh");
}

void finalize_inductive() {
    delete g_ind_fresh;
}
}
