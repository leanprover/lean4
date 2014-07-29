/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "kernel/type_checker.h"
#include "kernel/record/record.h"

namespace lean { namespace record {
static name g_tmp_prefix = name::mk_internal_unique_name();

/** \brief Environment extension used to store record information */
struct record_env_ext : public environment_extension {
    struct record_info {
        list<field>  m_fields;
    };

    // mapping from introduction rule name to computation rule data
    rb_map<name, record_info, name_quick_cmp>           m_record_info;
    record_env_ext() {}
};

/** \brief Helper functional object for processing record declarations. */
struct add_record_fn {
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    environment               m_env;
    name_generator            m_ngen;
    type_checker_ptr          m_tc;
    level_param_names const & m_level_params;
    name const &              m_record_name;
    expr const &              m_record_type;
    name const &              m_intro_name;
    expr const &              m_intro_type;
    add_record_fn(environment const & env, level_param_names const & level_params, name const & rec_name, expr const & rec_type,
                  name const & intro_name, expr const & intro_type):
        m_env(env), m_ngen(g_tmp_prefix), m_tc(new type_checker(m_env)),
        m_level_params(level_params), m_record_name(rec_name), m_record_type(rec_type),
        m_intro_name(intro_name), m_intro_type(intro_type) {}

    environment operator()() {
        // TODO(Leo):
        std::cout << m_record_name << " : " << m_record_type << "\n";
        std::cout << "   >> " << m_intro_name << " : " << m_intro_type << "\n";
        return m_env;
    }
};

environment add_record(environment const & env, level_param_names const & level_params, name const & rec_name, expr const & rec_type,
                       name const & intro_name, expr const & intro_type) {
    return add_record_fn(env, level_params, rec_name, rec_type, intro_name, intro_type)();
}

optional<expr> record_normalizer_extension::operator()(expr const &, extension_context &) const {
    return optional<expr>();
}

bool record_normalizer_extension::may_reduce_later(expr const &, extension_context &) const {
    return false;
}

bool record_normalizer_extension::supports(name const &) const {
    return false;
}
}}
