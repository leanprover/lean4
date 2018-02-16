/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception_with_pos.h"

namespace lean {
/** \brief Exception produced by a Lean parser. */
class parser_exception : public exception_with_pos {
protected:
    std::string           m_fname;
    pos_info              m_pos;
    optional<std::string> m_what_buffer;
public:
    parser_exception(char const * msg, char const * fname, pos_info pos):
            exception_with_pos(msg), m_fname(fname), m_pos(pos) {}
    parser_exception(std::string const & msg, char const * fname, pos_info pos):
            exception_with_pos(msg), m_fname(fname), m_pos(pos) {}
    parser_exception(sstream const & strm, char const * fname, pos_info pos):
            exception_with_pos(strm), m_fname(fname), m_pos(pos) {}
    virtual char const * what() const noexcept override;
    virtual optional<pos_info> get_pos() const override { return some(m_pos); }
    std::string const & get_file_name() const { return m_fname; }
    std::string const & get_msg() const { return m_msg; }
    virtual throwable * clone() const override { return new parser_exception(m_msg, m_fname.c_str(), m_pos); }
    virtual void rethrow() const override { throw *this; }
};
}
