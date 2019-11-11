/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <memory>
#include "util/rb_map.h"
#include "library/pos_info_provider.h"

namespace lean {
/* Temporary object for providing position information.
   It is only used for exceptions such as parser_nested_exception.
   The idea is to avoid storing the whole parser object in these exceptions. */
class parser_pos_provider : public pos_info_provider {
    std::string    m_strm_name;
    pos_info       m_pos;
public:
    parser_pos_provider(std::string const & strm_name, pos_info const & some_pos):
        m_strm_name(strm_name), m_pos(some_pos) {}
    virtual ~parser_pos_provider() {}
    virtual pos_info get_some_pos() const override { return m_pos; }
    virtual char const * get_file_name() const override { return m_strm_name.c_str(); }
};
}
