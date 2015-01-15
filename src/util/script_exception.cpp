/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include <cstdlib>
#include "util/thread.h"
#include "util/debug.h"
#include "util/script_exception.h"

namespace lean {
script_exception::script_exception(char const * lua_error) {
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

script_exception::~script_exception() {
}

char const * script_exception::get_file_name() const {
    lean_assert(get_source() == source::File);
    return m_file.c_str();
}

unsigned script_exception::get_line() const {
    lean_assert(get_source() != source::Unknown);
    return m_line;
}

char const * script_exception::get_msg() const noexcept {
    return exception::what();
}

MK_THREAD_LOCAL_GET_DEF(std::string, get_g_buffer)

char const * script_exception::what() const noexcept {
    std::string & buffer = get_g_buffer();
    std::ostringstream strm;
    char const * msg = get_msg();
    char const * space = msg && *msg == ' ' ? "" : " ";
    switch (get_source()) {
    case source::String:  strm << "[string]:" << get_line() << ":" << space << get_msg(); break;
    case source::File:    strm << get_file_name() << ":" << get_line() << ":" << space << get_msg(); break;
    case source::Unknown: return get_msg();
    }
    buffer = strm.str();
    return buffer.c_str();
}

script_nested_exception::script_nested_exception(source s, std::string f, unsigned l, std::shared_ptr<throwable> const & ex):
    script_exception(s, f, l, "Lean exception"),
    m_exception(ex) {
    lean_assert(ex);
}

script_nested_exception::~script_nested_exception() {}

char const * script_nested_exception::what() const noexcept {
    std::string super_what  = script_exception::what();
    std::string nested_what = get_exception().what();
    {
        std::string buffer;
        std::ostringstream strm;
        strm << super_what << "\n" << nested_what;
        buffer = strm.str();
        std::string & r_buffer = get_g_buffer();
        r_buffer = buffer;
        return r_buffer.c_str();
    }
}
}
