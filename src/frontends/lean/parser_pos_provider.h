/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <memory>
#include <unordered_map>
#include "kernel/pos_info_provider.h"

namespace lean {
typedef std::unordered_map<unsigned, pos_info> pos_info_table;
typedef std::shared_ptr<pos_info_table> pos_info_table_ptr;

class parser_pos_provider : public pos_info_provider {
    pos_info_table_ptr m_pos_table;
    std::string        m_strm_name;
    pos_info           m_pos;
public:
    parser_pos_provider(pos_info_table_ptr const & pos_table, std::string const & strm_name, pos_info const & some_pos);
    virtual ~parser_pos_provider();
    virtual optional<pos_info> get_pos_info(expr const & e) const;
    virtual pos_info get_some_pos() const;
    virtual char const * get_file_name() const;
};
}
