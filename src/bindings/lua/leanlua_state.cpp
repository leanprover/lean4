/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include <mutex>
#include <string>
#include "util/debug.h"
#include "util/exception.h"
#include "util/memory.h"
#include "bindings/lua/leanlua_state.h"

#ifdef LEAN_USE_LUA
#include <lua.hpp>
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"
#include "bindings/lua/options.h"
#include "bindings/lua/sexpr.h"
#include "bindings/lua/format.h"

extern "C" void * lua_realloc(void *, void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }

namespace lean {
struct leanlua_state::imp {
    lua_State * m_state;
    std::mutex  m_mutex;

    imp() {
        #ifdef LEAN_USE_LUA_NEWSTATE
        m_state = lua_newstate(lua_realloc, nullptr);
        #else
        m_state = luaL_newstate();
        #endif
        if (m_state == nullptr)
            throw exception("fail to create Lua interpreter");
        luaL_openlibs(m_state);
        lean::open_name(m_state);
        lean::open_mpz(m_state);
        lean::open_mpq(m_state);
        lean::open_options(m_state);
        lean::open_sexpr(m_state);
        lean::open_format(m_state);
    }

    ~imp() {
        lua_close(m_state);
    }

    void exec() {
        int result = lua_pcall(m_state, 0, LUA_MULTRET, 0);
        if (result)
            throw lua_exception(lua_tostring(m_state, -1));
    }

    void dofile(char const * fname) {
        std::lock_guard<std::mutex> lock(m_mutex);
        int result = luaL_loadfile(m_state, fname);
        if (result)
            throw lua_exception(lua_tostring(m_state, -1));
        exec();
    }

    void dostring(char const * str) {
        std::lock_guard<std::mutex> lock(m_mutex);
        int result = luaL_loadstring(m_state, str);
        if (result)
            throw lua_exception(lua_tostring(m_state, -1));
        exec();
    }
};

leanlua_state::leanlua_state():
    m_ptr(new imp()) {
}

leanlua_state::~leanlua_state() {
}

void leanlua_state::dofile(char const * fname) {
    m_ptr->dofile(fname);
}

void leanlua_state::dostring(char const * str) {
    m_ptr->dostring(str);
}
}
#else
namespace lean {
leanlua_state::leanlua_state() {
}

leanlua_state::~leanlua_state() {
}

[[ noreturn ]] void throw_lua_not_supported() {
    throw exception("Lean was compiled without Lua support");
}

void leanlua_state::dofile(char const * fname) {
    throw_lua_not_supported();
}

void leanlua_state::dostring(char const * str) {
    throw_lua_not_supported();
}
}
#endif

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
    case source::File:    strm << m_file << ":" << m_file << ":" << msg() << "\n"; break;
    case source::Unknown: return msg();
    }
    buffer = strm.str();
    return buffer.c_str();
}
}
