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
#include "kernel/expr.h"
#include "kernel/pos_info_provider.h"
#include "library/io_state_stream.h"

namespace lean {
/** \brief Datastructure for storing where a given declaration was defined. */
class declaration_index {
    enum class entry_kind { Declaration, Reference };
    typedef std::tuple<entry_kind, std::string, pos_info, name, name, expr> entry;
    std::vector<entry> m_entries;
public:
    void add_decl(std::string const fname, pos_info const & p, name const & n, name const & k, expr const & t);
    void add_ref(std::string const fname, pos_info const & p, name const & n);
    void save(io_state_stream const & out) const;
};
}
