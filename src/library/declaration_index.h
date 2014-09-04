/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <vector>
#include <utility>
#include <string>
#include "util/name.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/pos_info_provider.h"
#include "library/io_state_stream.h"

namespace lean {
/** \brief Datastructure for storing where a given declaration was defined. */
class declaration_index {
    typedef std::tuple<std::string, pos_info, name, expr> decl;
    typedef std::tuple<std::string, pos_info, name> ref;
    typedef pair<name, name> abbrev;
    name_map<decl>      m_decls;
    std::vector<abbrev> m_abbrevs;
    std::vector<ref>    m_refs;
public:
    void add_decl(std::string const fname, pos_info const & p, name const & n, name const & k, expr const & t);
    void add_abbrev(name const & n, name const & d);
    void add_ref(std::string const fname, pos_info const & p, name const & n);
    void save(io_state_stream const & out) const;
};
}
