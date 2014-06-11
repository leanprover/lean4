/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "frontends/lean/parser_pos_provider.h"

namespace lean {
parser_pos_provider::parser_pos_provider(pos_info_table_ptr const & pos_table,
                                                   std::string const & strm_name, pos_info const & some_pos):
    m_pos_table(pos_table), m_strm_name(strm_name), m_pos(some_pos) {}

parser_pos_provider::~parser_pos_provider() {}

std::pair<unsigned, unsigned> parser_pos_provider::get_pos_info(expr const & e) const {
    if (!m_pos_table)
        return get_some_pos();
    tag t = e.get_tag();
    if (t == nulltag)
        return get_some_pos();
    auto it = m_pos_table->find(t);
    if (it == m_pos_table->end())
        return get_some_pos();
    return it->second;
}

std::pair<unsigned, unsigned> parser_pos_provider::get_some_pos() const {
    return m_pos;
}

char const * parser_pos_provider::get_file_name() const {
    return m_strm_name.c_str();
}
}
