/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include <cstdlib>
#include "util/debug.h"
#include "bindings/lua/lua_exception.h"

namespace lean {
lua_exception::lua_exception(char const * lua_error):exception("") {
    lean_assert(lua_error);
    std::string fname;
    std::string line;
    std::string msg;
    int state = 0;
    char const * it = lua_error;
    while (*it) {
        if (state == 0) {
            if (*it == ':') {
                state = 1;
            } else {
                fname += *it;
            }
        } else if (state == 1) {
            if (*it == ':') {
                state = 2;
            } else {
                line += *it;
            }
        } else {
            msg += *it;
        }
        it++;
    }
    if (state != 2) {
        // failed to decode Lua error message
        m_source = source::Unknown;
        m_msg = lua_error;
    } else {
        if (fname == "[string \"...\"]") {
            m_source = source::String;
        } else {
            m_source = source::File;
            m_file   = fname;
        }
        m_line   = atoi(line.c_str());
        m_msg = msg;
    }
}

char const * lua_exception::get_filename() const {
    lean_assert(get_source() == source::File);
    return m_file.c_str();
}

unsigned lua_exception::get_line() const {
    lean_assert(get_source() != source::Unknown);
    return m_line;
}

char const * lua_exception::msg() const noexcept {
    return exception::what();
}

char const * lua_exception::what() const noexcept {
    static thread_local std::string buffer;
    std::ostringstream strm;
    switch (m_source) {
    case source::String:  strm << "[string]:" << m_line << ":" << msg() << "\n"; break;
    case source::File:    strm << m_file << ":" << m_line << ":" << msg() << "\n"; break;
    case source::Unknown: return msg();
    }
    buffer = strm.str();
    return buffer.c_str();
}
}
