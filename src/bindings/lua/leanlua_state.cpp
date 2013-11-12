/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <mutex>
#include <thread>
#include <string>
#include <lua.hpp>
#include "util/debug.h"
#include "util/exception.h"
#include "util/memory.h"
#include "util/buffer.h"
#include "bindings/lua/leanlua_state.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"
#include "bindings/lua/options.h"
#include "bindings/lua/sexpr.h"
#include "bindings/lua/format.h"
#include "bindings/lua/level.h"
#include "bindings/lua/local_context.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/object.h"
#include "bindings/lua/environment.h"
#include "bindings/lua/lean.lua"

extern "C" void * lua_realloc(void *, void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }

namespace lean {
static void open_patch(lua_State * L);
static void open_state(lua_State * L);
static void open_thread(lua_State * L);
environment & to_environment(lua_State * L, int idx);
static int writer(lua_State *, void const * p, size_t sz, void * buf) {
    buffer<char> & _buf = *static_cast<buffer<char>*>(buf);
    char const * in = static_cast<char const *>(p);
    for (size_t i = 0; i < sz; i++)
        _buf.push_back(in[i]);
    return 0;
}
struct reader_data {
    buffer<char> & m_buffer;
    bool           m_done;
    reader_data(buffer<char> & b):m_buffer(b), m_done(false) {}
};
static char const * reader(lua_State *, void * data, size_t * sz) {
    reader_data & _data = *static_cast<reader_data*>(data);
    if (_data.m_done) {
        *sz = 0;
        return nullptr;
    } else {
        *sz = _data.m_buffer.size();
        _data.m_done = true;
        return _data.m_buffer.data();
    }
}

static void copy_values(lua_State * src, int first, int last, lua_State * tgt) {
    for (int i = first; i <= last; i++) {
        if (lua_isstring(src, i)) {
            lua_pushfstring(tgt, lua_tostring(src, i));
        } else if (lua_isnumber(src, i)) {
            lua_pushnumber(tgt, lua_tonumber(src, i));
        } else if (lua_isboolean(src, i)) {
            lua_pushboolean(tgt, lua_toboolean(src, i));
        } else if (lua_isfunction(src, i)) {
            lua_pushvalue(src, i); // copy function to the top of the stack
            buffer<char> buffer;
            if (lua_dump(src, writer, &buffer) != 0)
                throw exception("falied to copy function between State objects");
            lua_pop(src, 1); // remove function from the top of the stack
            reader_data data(buffer);
            if (load(tgt, reader, &data, "temporary buffer for moving functions between states") != 0)
                throw exception("falied to copy function between State objects");
            // copy upvalues
            int j = 1;
            while (true) {
                char const * name = lua_getupvalue(src, i, j);
                if (name == nullptr)
                    break;
                copy_values(src, lua_gettop(src), lua_gettop(src), tgt); // copy upvalue to tgt stack
                lua_pop(src, 1); // remove upvalue from src stack
                lua_setupvalue(tgt, -2, j);
                j++;
            }
        } else if (is_expr(src, i)) {
            push_expr(tgt, to_expr(src, i));
        } else if (is_context(src, i)) {
            push_context(tgt, to_context(src, i));
        } else if (is_environment(src, i)) {
            push_environment(tgt, to_environment(src, i));
        } else if (is_name(src, i)) {
            push_name(tgt, to_name(src, i));
        } else if (is_mpz(src, i)) {
            push_mpz(tgt, to_mpz(src, i));
        } else if (is_mpq(src, i)) {
            push_mpq(tgt, to_mpq(src, i));
        } else if (is_options(src, i)) {
            push_options(tgt, to_options(src, i));
        } else if (is_sexpr(src, i)) {
            push_sexpr(tgt, to_sexpr(src, i));
        } else if (is_format(src, i)) {
            push_format(tgt, to_format(src, i));
        } else if (is_context_entry(src, i)) {
            push_context_entry(tgt, to_context_entry(src, i));
        } else if (is_local_context(src, i)) {
            push_local_context(tgt, to_local_context(src, i));
        } else if (is_local_entry(src, i)) {
            push_local_entry(tgt, to_local_entry(src, i));
        } else {
            throw exception("unsupported value type for inter-State call");
        }
    }
}

struct leanlua_state::imp {
    lua_State * m_state;
    std::mutex  m_mutex;

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
        luaL_openlibs(m_state);
        open_patch(m_state);
        open_name(m_state);
        open_mpz(m_state);
        open_mpq(m_state);
        open_options(m_state);
        open_sexpr(m_state);
        open_format(m_state);
        open_level(m_state);
        open_local_context(m_state);
        open_expr(m_state);
        open_context(m_state);
        open_object(m_state);
        open_environment(m_state);
        open_state(m_state);
        open_thread(m_state);
        dostring(g_leanlua_extra);
    }

    ~imp() {
        lua_close(m_state);
    }

    void dofile(char const * fname) {
        std::lock_guard<std::mutex> lock(m_mutex);
        ::lean::dofile(m_state, fname);
    }

    void dostring(char const * str) {
        std::lock_guard<std::mutex> lock(m_mutex);
        ::lean::dostring(m_state, str);
    }

    void dostring(char const * str, environment & env) {
        set_environment set(m_state, env);
        dostring(str);
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

void leanlua_state::dostring(char const * str, environment & env) {
    m_ptr->dostring(str, env);
}

static std::mutex g_print_mutex;

/** \brief Thread safe version of print function */
static int print(lua_State * L) {
    // TODO(Leo): use output channels (if available) instead of std::cout
    int n = lua_gettop(L);
    int i;
    lua_getglobal(L, "tostring");
    std::lock_guard<std::mutex> lock(g_print_mutex);
    for (i = 1; i <= n; i++) {
        char const * s;
        size_t l;
        lua_pushvalue(L, -1);
        lua_pushvalue(L, i);
        lua_call(L, 1, 1);
        s = lua_tolstring(L, -1, &l);
        if (s == NULL)
            throw exception("'to_string' must return a string to 'print'");
        if (i > 1) {
            std::cout << "\t";
        }
        std::cout << s;
        lua_pop(L, 1);
    }
    std::cout << std::endl;
    return 0;
}

/** \brief Redefine some functions from the Lua library */
static void open_patch(lua_State * L) {
    set_global_function<print>(L, "print");
}

constexpr char const * state_mt = "state.mt";

bool is_state(lua_State * L, int idx) {
    return testudata(L, idx, state_mt);
}

leanlua_state & to_state(lua_State * L, int idx) {
    return *static_cast<leanlua_state*>(luaL_checkudata(L, idx, state_mt));
}

int push_state(lua_State * L, leanlua_state const & s) {
    void * mem = lua_newuserdata(L, sizeof(leanlua_state));
    new (mem) leanlua_state(s);
    luaL_getmetatable(L, state_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_state(lua_State * L) {
    leanlua_state r;
    return push_state(L, r);
}

static int state_gc(lua_State * L) {
    to_state(L, 1).~leanlua_state();
    return 0;
}

int state_dostring(lua_State * L) {
    auto S = to_state(L, 1).m_ptr;
    char const * script = luaL_checkstring(L, 2);
    int first           = 3;
    int last            = lua_gettop(L);
    std::lock_guard<std::mutex> lock(S->m_mutex);

    int sz_before = lua_gettop(S->m_state);

    int result = luaL_loadstring(S->m_state, script);
    if (result)
        throw lua_exception(lua_tostring(S->m_state, -1));

    copy_values(L, first, last, S->m_state);

    result = lua_pcall(S->m_state, first > last ? 0 : last - first + 1, LUA_MULTRET, 0);
    if (result)
        throw lua_exception(lua_tostring(S->m_state, -1));

    int sz_after = lua_gettop(S->m_state);

    if (sz_after > sz_before) {
        copy_values(S->m_state, sz_before + 1, sz_after, L);
        lua_pop(S->m_state, sz_after - sz_before);
    }
    return sz_after - sz_before;
}

int state_set_global(lua_State * L) {
    auto S = to_state(L, 1).m_ptr;
    char const * name = luaL_checkstring(L, 2);
    std::lock_guard<std::mutex> lock(S->m_mutex);
    copy_values(L, 3, 3, S->m_state);
    lua_setglobal(S->m_state, name);
    return 0;
}

static int state_pred(lua_State * L) {
    lua_pushboolean(L, is_state(L, 1));
    return 1;
}

static const struct luaL_Reg state_m[] = {
    {"__gc",            state_gc},
    {"dostring",        safe_function<state_dostring>},
    {"eval",            safe_function<state_dostring>},
    {"set",             safe_function<state_set_global>},
    {0, 0}
};

static void open_state(lua_State * L) {
    luaL_newmetatable(L, state_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, state_m, 0);

    set_global_function<mk_state>(L, "State");
    set_global_function<state_pred>(L, "is_State");
}

class leanlua_thread {
    leanlua_state m_state;
    int           m_sz_before;
    bool          m_error;
    std::string   m_error_msg;
    std::thread   m_thread;
public:
    leanlua_thread(leanlua_state const & st, int sz_before, int num_args):
        m_state(st),
        m_sz_before(sz_before),
        m_error(false),
        m_thread([=]() {
                auto S = m_state.m_ptr;
                std::lock_guard<std::mutex> lock(S->m_mutex);
                int result = lua_pcall(S->m_state, num_args, LUA_MULTRET, 0);
                if (result) {
                    m_error = true;
                    m_error_msg = lua_tostring(S->m_state, -1);
                    return;
                }
            }) {
    }

    ~leanlua_thread() {
        if (m_thread.joinable())
            m_thread.join();
    }

    int wait(lua_State * src) {
        m_thread.join();
        if (m_error)
            throw lua_exception(m_error_msg.c_str());
        auto S = m_state.m_ptr;
        int sz_after = lua_gettop(S->m_state);

        if (sz_after > m_sz_before) {
            copy_values(S->m_state, m_sz_before + 1, sz_after, src);
            lua_pop(S->m_state, sz_after - m_sz_before);
        }
        return sz_after - m_sz_before;
    }
};

constexpr char const * thread_mt = "thread.mt";

bool is_thread(lua_State * L, int idx) {
    return testudata(L, idx, thread_mt);
}

leanlua_thread & to_thread(lua_State * L, int idx) {
    return *static_cast<leanlua_thread*>(luaL_checkudata(L, idx, thread_mt));
}

int mk_thread(lua_State * L) {
    leanlua_state & st  = to_state(L, 1);
    char const * script = luaL_checkstring(L, 2);
    int first           = 3;
    int last            = lua_gettop(L);
    int nargs           = first > last ? 0 : last - first + 1;
    int sz_before;
    auto S = st.m_ptr;
    {
        std::lock_guard<std::mutex> lock(S->m_mutex);
        sz_before = lua_gettop(S->m_state);
        int result  = luaL_loadstring(S->m_state, script);
        if (result)
            throw lua_exception(lua_tostring(S->m_state, -1));
        copy_values(L, first, last, S->m_state);
    }
    void * mem = lua_newuserdata(L, sizeof(leanlua_thread));
    new (mem) leanlua_thread(st, sz_before, nargs);
    luaL_getmetatable(L, thread_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int thread_gc(lua_State * L) {
    to_thread(L, 1).~leanlua_thread();
    return 0;
}

static int thread_pred(lua_State * L) {
    lua_pushboolean(L, is_thread(L, 1));
    return 1;
}

int thread_wait(lua_State * L) {
    return to_thread(L, 1).wait(L);
}

static const struct luaL_Reg thread_m[] = {
    {"__gc",    thread_gc},
    {"wait",    safe_function<thread_wait>},
    {0, 0}
};

static void open_thread(lua_State * L) {
    luaL_newmetatable(L, thread_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, thread_m, 0);

    set_global_function<mk_thread>(L, "thread");
    set_global_function<thread_pred>(L, "is_thread");
}
}
