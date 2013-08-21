/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <map>
#include "options.h"

namespace lean {
/**
   \brief Datastructure for storing information about available
   configuration options.
*/
class option_declaration {
    name        m_name;
    option_kind m_kind;
    std::string m_default;
    std::string m_description;
public:
    option_declaration(name const & n, option_kind k, char const * default_val, char const * descr):
        m_name(n), m_kind(k), m_default(default_val), m_description(descr) {}
    option_kind kind() const { return m_kind; }
    name const & get_name() const { return m_name; }
    std::string const & get_default_value() const { return m_default; }
    std::string const & get_description() const { return m_description; }
};

typedef std::map<name, option_declaration> option_declarations;
option_declarations const & get_option_declarations();
}
