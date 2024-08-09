/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <map>
#include <string>
#include "util/macros.h"
#include "util/name_map.h"
#include "util/options.h"

namespace lean {
/**
   \brief Datastructure for storing information about available
   configuration options.
*/
class option_declaration {
    name            m_name;
    data_value_kind m_kind;
    std::string     m_default;
    std::string     m_description;
public:
    option_declaration() {}
    option_declaration(name const & n, data_value_kind k, char const * default_val, char const * descr):
        m_name(n), m_kind(k), m_default(default_val), m_description(descr) {}
    data_value_kind kind() const { return m_kind; }
    name const & get_name() const { return m_name; }
    std::string const & get_default_value() const { return m_default; }
    std::string const & get_description() const { return m_description; }
    /** \brief Display value of this option declaration in \c o.
        \remark if \c o does not set this option, then the default value is displayed. */
    void display_value(std::ostream & out, options const & o) const;
};

typedef name_map<option_declaration> option_declarations;
LEAN_EXPORT option_declarations get_option_declarations();
void register_option(name const & n, name const & decl_name, data_value_kind k, char const * default_value, char const * description);
#define register_bool_option(n, v, d) register_option(n, {}, data_value_kind::Bool, LEAN_STR(v), d)
#define register_unsigned_option(n, v, d) register_option(n, {}, data_value_kind::Nat, LEAN_STR(v), d)
#define register_string_option(n, v, d) register_option(n, {}, data_value_kind::String, LEAN_STR(v), d)
}
