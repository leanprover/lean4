/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include <vector>
#include <unordered_set>
#include "util/lua.h"
#include "util/debug.h"
#include "util/exception.h"
#include "util/memory.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/script_state.h"
#include "util/script_exception.h"
#include "util/name.h"
#include "util/name_generator.h"
#include "util/name_set.h"
#include "util/rb_map.h"
#include "util/lean_path.h"

extern "C" void * lua_realloc(void *, void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }

namespace lean {
static std::vector<script_state::reg_fn> * g_modules = nullptr;

void script_state::register_module(reg_fn f) {
    g_modules->push_back(f);
}

void initialize_script_state() {
    g_modules = new std::vector<script_state::reg_fn>();
}

void finalize_script_state() {
    delete g_modules;
}

static unsigned g_check_interrupt_freq = 1048576;

void script_state::set_check_interrupt_freq(unsigned count) {
    g_check_interrupt_freq = count;
}

void open_extra(lua_State * L);

static char g_weak_ptr_key; // key for Lua registry (used at get_weak_ptr and save_weak_ptr)

struct script_state::imp {
    lua_State * m_state;
    std::unordered_set<std::string> m_imported_modules;

    static std::weak_ptr<imp> * get_weak_ptr(lua_State * L) {
        lua_pushlightuserdata(L, static_cast<void *>(&g_weak_ptr_key));
        lua_gettable(L, LUA_REGISTRYINDEX);
        std::weak_ptr<imp> * ptr = static_cast<std::weak_ptr<imp>*>(lua_touserdata(L, -1));
        lua_pop(L, 1);
        return ptr;
    }

    void save_weak_ptr(std::shared_ptr<imp> & ptr) {
        lua_pushlightuserdata(m_state, static_cast<void *>(&g_weak_ptr_key));
        void * mem = lua_newuserdata(m_state, sizeof(std::weak_ptr<imp>));
        new (mem) std::weak_ptr<imp>(ptr);
        lua_settable(m_state, LUA_REGISTRYINDEX);
    }

    static void check_interrupted_hook(lua_State * L, lua_Debug *) {
        try {
            check_interrupted();
        } catch (interrupted & ex) {
            push_exception(L, ex);
            lua_error(L);
        }
    }

    imp() {
        // TODO(Leo) investigate why TCMALLOC + lua_realloc do not work together
        // #ifdef LEAN_USE_LUA_NEWSTATE
        #if 0
        m_state = lua_newstate(lua_realloc, nullptr);
        #else
        m_state = luaL_newstate();
        #endif
        if (m_state == nullptr)
            throw exception("fail to create Lua interpreter");
        if (g_check_interrupt_freq > 0) {
            lua_sethook(m_state, check_interrupted_hook, LUA_MASKCOUNT, g_check_interrupt_freq);
        }
        if (!lua_checkstack(m_state, 1024))
            throw exception("lua_checkstack failed");
        luaL_openlibs(m_state);
        open_exception(m_state);
        open_name(m_state);
        open_name_generator(m_state);
        open_name_set(m_state);
        open_rb_map(m_state);
        open_extra(m_state);

        for (auto f : *g_modules) {
            f(m_state);
        }
    }

    ~imp() {
        typedef std::weak_ptr<imp> wptr;
        wptr * ptr = get_weak_ptr(m_state);
        ptr->~wptr(); // destruct weak pointer
        lua_close(m_state);
    }

    void dofile(char const * fname) {
        ::lean::dofile(m_state, fname);
    }

    void dostring(char const * str) {
        ::lean::dostring(m_state, str);
    }

    bool import_explicit(std::string const & fname) {
        if (m_imported_modules.find(fname) == m_imported_modules.end()) {
            dofile(fname.c_str());
            m_imported_modules.insert(fname);
            return true;
        } else {
            return false;
        }
    }

    bool import_explicit(char const * fname) {
        return import_explicit(std::string(fname));
    }

    bool import(char const * fname) {
        return import_explicit(find_file(std::string(fname)));
    }
};

script_state to_script_state(lua_State * L) {
    return script_state(*script_state::imp::get_weak_ptr(L));
}

script_state::script_state():
    m_ptr(std::make_shared<imp>()) {
    m_ptr->save_weak_ptr(m_ptr);
}

script_state::script_state(weak_ref const & r) {
    if (r.expired())
        throw exception("weak reference to script_state object has expired (i.e., it has been deleted)");
    m_ptr = r.lock();
}

script_state::~script_state() {
}

void script_state::dofile(char const * fname) {
    m_ptr->dofile(fname);
}

void script_state::dostring(char const * str) {
    m_ptr->dostring(str);
}

bool script_state::import(char const * str) {
    return m_ptr->import(str);
}

bool script_state::import_explicit(char const * str) {
    return m_ptr->import_explicit(str);
}

lua_State * script_state::get_state() {
    return m_ptr->m_state;
}

static int check_interrupted(lua_State *) { // NOLINT
    check_interrupted();
    return 0;
}

static int sleep(lua_State * L) {
    sleep_for(luaL_checkinteger(L, 1));
    return 0;
}

static int yield(lua_State * L) {
    check_interrupted();
    int status = lua_pushthread(L);
    lua_pop(L, 1);
    if (status != 1) {
        return lua_yield(L, 0);
    } else {
        // main thread cannot yield
        return 0;
    }
}

static int import(lua_State * L) {
    std::string fname = luaL_checkstring(L, 1);
    script_state s = to_script_state(L);
    s.import(fname.c_str());
    return 0;
}

void open_extra(lua_State * L) {
    SET_GLOBAL_FUN(check_interrupted, "check_interrupted");
    SET_GLOBAL_FUN(sleep,             "sleep");
    SET_GLOBAL_FUN(yield,             "yield");
    SET_GLOBAL_FUN(import,            "import");
}
}
