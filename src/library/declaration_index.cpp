/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/declaration_index.h"

namespace lean {
void declaration_index::add_decl(std::string const fname, pos_info const & p, name const & n, name const & k, expr const & t) {
    m_decls.insert(n, decl(fname, p, k, t));
}
void declaration_index::add_abbrev(name const & n, name const & d) {
    m_abbrevs.emplace_back(n, d);
}
void declaration_index::add_ref(std::string const fname, pos_info const & p, name const & n) {
    m_refs.emplace_back(fname, p, n);
}
void declaration_index::save(io_state_stream const & out) const {
    std::string fname; pos_info p; name n, k; expr t;
    options const & opts = out.get_options();
    m_decls.for_each([&](name const & n, decl const & d) {
            std::tie(fname, p, k, t) = d;
            out << "d" << "|" << fname << "|" << p.first << "|" << p.second << "|" << n;
            out << "|" << k << "|";
            out.get_stream() << mk_pair(flatten(out.get_formatter()(t)), opts);
            out << endl;
        });
    for (auto const & a : m_abbrevs) {
        out << "a" << "|" << a.first << "|" << a.second << endl;
    }
    for (auto const & r : m_refs) {
        std::tie(fname, p, n) = r;
        out << "r" << "|" << fname << "|" << p.first << "|" << p.second << "|" << n << endl;
    }
}
}
