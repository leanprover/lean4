/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
namespace lean {
class simple_pos_info_provider : public pos_info_provider {
    char const * m_fname;
public:
    simple_pos_info_provider(char const * fname):m_fname(fname) {}
    virtual optional<pos_info> get_pos_info(expr const &) const { return optional<pos_info>(); }
    virtual char const * get_file_name() const { return m_fname; }
    virtual pos_info get_some_pos() const { return pos_info(-1, -1); }
};
}
