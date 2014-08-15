/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/declaration_index.h"

namespace lean {
void declaration_index::add_decl(std::string const fname, pos_info const & p, name const & n) {
    m_entries.emplace_back(entry_kind::Declaration, fname, p, n);
}
void declaration_index::add_ref(std::string const fname, pos_info const & p, name const & n) {
    m_entries.emplace_back(entry_kind::Reference, fname, p, n);
}
void declaration_index::save(std::ostream & out) const {
    entry_kind k; std::string fname; pos_info p; name n;
    for (auto const & e : m_entries) {
        std::tie(k, fname, p, n) = e;
        out << (k == entry_kind::Declaration ? "d" : "r") << "|" << fname << "|" << p.first
            << "|" << p.second << "|" << n << std::endl;
    }
}
}
