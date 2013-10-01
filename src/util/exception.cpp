/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/exception.h"
#include "util/sstream.h"

namespace lean {
exception::exception(char const * msg):m_msg(msg) {}
exception::exception(std::string const & msg):m_msg(msg) {}
exception::exception(sstream const & strm):m_msg(strm.str()) {}
exception::~exception() noexcept {}
char const * exception::what() const noexcept { return m_msg.c_str(); }

parser_exception::parser_exception(char const * msg, unsigned l, unsigned p):exception(msg), m_line(l), m_pos(p) {}
parser_exception::parser_exception(std::string const & msg, unsigned l, unsigned p):exception(msg), m_line(l), m_pos(p) {}
parser_exception::parser_exception(sstream const & msg, unsigned l, unsigned p):exception(msg), m_line(l), m_pos(p) {}
parser_exception::~parser_exception() noexcept {}
char const * parser_exception::what() const noexcept {
    try {
        static thread_local std::string buffer;
        std::ostringstream s;
        s << "(line: " << m_line << ", pos: " << m_pos << ") " << m_msg;
        buffer = s.str();
        return buffer.c_str();
    } catch (std::exception & ex) {
        // failed to generate extended message
        return m_msg.c_str();
    }
}
}
