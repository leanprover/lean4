/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/thread.h"

namespace lean {
throwable::throwable(char const * msg):m_msg(msg) {}
throwable::throwable(std::string const & msg):m_msg(msg) {}
throwable::throwable(sstream const & strm):m_msg(strm.str()) {}
throwable::~throwable() noexcept {}
char const * throwable::what() const noexcept { return m_msg.c_str(); }

parser_exception::parser_exception(char const * msg, char const * fname, unsigned l, unsigned p):
    exception(msg), m_fname(fname), m_line(l), m_pos(p) {}
parser_exception::parser_exception(std::string const & msg, char const * fname, unsigned l, unsigned p):
    exception(msg), m_fname(fname), m_line(l), m_pos(p) {}
parser_exception::parser_exception(sstream const & msg, char const * fname, unsigned l, unsigned p):
    exception(msg), m_fname(fname), m_line(l), m_pos(p) {}
parser_exception::~parser_exception() noexcept {}
MK_THREAD_LOCAL_GET_DEF(std::string, get_g_buffer);
char const * parser_exception::what() const noexcept {
    try {
        std::string & buffer = get_g_buffer();
        std::ostringstream s;
        s << m_fname << ":" << m_line << ":" << m_pos << ": error: " << m_msg;
        buffer = s.str();
        return buffer.c_str();
    } catch (std::exception & ex) {
        // failed to generate extended message
        return m_msg.c_str();
    }
}

char const * stack_space_exception::what() const noexcept {
    std::string & buffer = get_g_buffer();
    std::ostringstream s;
    s << "deep recursion was detected at '" << m_component_name << "' (potential solution: increase stack space in your system)";
    buffer = s.str();
    return buffer.c_str();
}

char const * memory_exception::what() const noexcept {
    std::string & buffer = get_g_buffer();
    std::ostringstream s;
    s << "excessive memory consumption detected at '" << m_component_name << "' (potential solution: increase memory consumption threshold)";
    buffer = s.str();
    return buffer.c_str();
}
}
