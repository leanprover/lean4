/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "library/kernel_bindings.h"
#include "library/io_state.h"

namespace lean {
io_state::io_state():
    m_formatter(mk_simple_formatter()),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}

io_state::io_state(options const & opts, formatter const & fmt):
    m_options(opts),
    m_formatter(fmt),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}

io_state::~io_state() {}

void io_state::set_regular_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_regular_channel = out;
}

void io_state::set_diagnostic_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_diagnostic_channel = out;
}

void io_state::set_options(options const & opts) {
    m_options = opts;
}

void io_state::set_formatter(formatter const & f) {
    m_formatter = f;
}

io_state_stream const & operator<<(io_state_stream const & out, endl_class) {
    out.get_stream() << std::endl;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr const & e) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(e, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, object const & obj) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(obj, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, environment const & env) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(out.get_formatter()(env, opts), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, kernel_exception const & ex) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(ex.pp(out.get_formatter(), opts), opts);
    return out;
}

DECL_UDATA(io_state)

int mk_io_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_io_state(L, io_state());
    else if (nargs == 1)
        return push_io_state(L, io_state(to_io_state(L, 1)));
    else
        return push_io_state(L, io_state(to_options(L, 1), to_formatter(L, 2)));
}

int io_state_get_options(lua_State * L) {
    return push_options(L, to_io_state(L, 1).get_options());
}

int io_state_get_formatter(lua_State * L) {
    return push_formatter(L, to_io_state(L, 1).get_formatter());
}

int io_state_set_options(lua_State * L) {
    to_io_state(L, 1).set_options(to_options(L, 2));
    return 0;
}

static mutex g_print_mutex;

static void print(io_state * ios, bool reg, char const * msg) {
    if (ios) {
        if (reg)
            regular(*ios) << msg;
        else
            diagnostic(*ios) << msg;
    } else {
        std::cout << msg;
    }
}

/** \brief Thread safe version of print function */
static int print(lua_State * L, int start, bool reg) {
    lock_guard<mutex> lock(g_print_mutex);
    io_state * ios = get_io_state(L);
    int n = lua_gettop(L);
    int i;
    lua_getglobal(L, "tostring");
    for (i = start; i <= n; i++) {
        char const * s;
        size_t l;
        lua_pushvalue(L, -1);
        lua_pushvalue(L, i);
        lua_call(L, 1, 1);
        s = lua_tolstring(L, -1, &l);
        if (s == NULL)
            throw exception("'to_string' must return a string to 'print'");
        if (i > start) {
            print(ios, reg, "\t");
        }
        print(ios, reg, s);
        lua_pop(L, 1);
    }
    print(ios, reg, "\n");
    return 0;
}

static int print(lua_State * L, io_state & ios, int start, bool reg) {
    set_io_state set(L, ios);
    return print(L, start, reg);
}

static int print(lua_State * L) {
    return print(L, 1, true);
}

int io_state_print_regular(lua_State * L) {
    return print(L, to_io_state(L, 1), 2, true);
}

int io_state_print_diagnostic(lua_State * L) {
    return print(L, to_io_state(L, 1), 2, false);
}

static const struct luaL_Reg io_state_m[] = {
    {"__gc",             io_state_gc}, // never throws
    {"get_options",      safe_function<io_state_get_options>},
    {"set_options",      safe_function<io_state_set_options>},
    {"get_formatter",    safe_function<io_state_get_formatter>},
    {"print_diagnostic", safe_function<io_state_print_diagnostic>},
    {"print_regular",    safe_function<io_state_print_regular>},
    {"print",            safe_function<io_state_print_regular>},
    {"diagnostic",       safe_function<io_state_print_diagnostic>},
    {0, 0}
};

void open_io_state(lua_State * L) {
    luaL_newmetatable(L, io_state_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, io_state_m, 0);

    SET_GLOBAL_FUN(io_state_pred, "is_io_state");
    SET_GLOBAL_FUN(mk_io_state, "io_state");
    SET_GLOBAL_FUN(print, "print");
}

static char g_set_state_key;

set_io_state::set_io_state(lua_State * L, io_state & st) {
    m_state = L;
    m_prev  = get_io_state(L);
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, &st);
    lua_settable(m_state, LUA_REGISTRYINDEX);
    if (!m_prev)
        m_prev_options = get_global_options(m_state);
    set_global_options(m_state, st.get_options());
}

set_io_state::~set_io_state() {
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, m_prev);
    lua_settable(m_state, LUA_REGISTRYINDEX);
    if (!m_prev)
        set_global_options(m_state, m_prev_options);
    else
        set_global_options(m_state, m_prev->get_options());
}

io_state * get_io_state(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_state_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_islightuserdata(L, -1)) {
        io_state * r = static_cast<io_state*>(lua_touserdata(L, -1));
        if (r) {
            lua_pop(L, 1);
            options o = get_global_options(L);
            r->set_options(o);
            return r;
        }
    }
    lua_pop(L, 1);
    return nullptr;
}
}
