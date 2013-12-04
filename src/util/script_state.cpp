/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <mutex>
#include <thread>
#include <chrono>
#include <string>
#include <vector>
#include <condition_variable>
#include "util/lua.h"
#include "util/debug.h"
#include "util/exception.h"
#include "util/memory.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/script_state.h"
#include "util/script_exception.h"
#include "util/name.h"
#include "util/splay_map.h"

extern "C" void * lua_realloc(void *, void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }

namespace lean {
static std::vector<script_state::reg_fn> g_modules;
static std::vector<char const *> g_code;

void script_state::register_module(reg_fn f) {
    g_modules.push_back(f);
}

void script_state::register_code(char const * code) {
    g_code.push_back(code);
}

void open_extra(lua_State * L);

static char g_weak_ptr_key; // key for Lua registry (used at get_weak_ptr and save_weak_ptr)

struct script_state::imp {
    lua_State * m_state;
    std::mutex  m_mutex;

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
        open_exception(m_state);
        open_name(m_state);
        open_splay_map(m_state);
        open_extra(m_state);

        for (auto f : g_modules) {
            f(m_state);
        }

        for (auto c : g_code) {
            dostring(c);
        }
    }

    ~imp() {
        typedef std::weak_ptr<imp> wptr;
        wptr * ptr = get_weak_ptr(m_state);
        ptr->~wptr(); // destruct weak pointer
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
};

script_state to_script_state(lua_State * L) {
    return script_state(*script_state::imp::get_weak_ptr(L));
}

script_state::script_state():
    m_ptr(new imp()) {
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

std::mutex & script_state::get_mutex() {
    return m_ptr->m_mutex;
}

lua_State * script_state::get_state() {
    return m_ptr->m_state;
}

constexpr char const * state_mt = "luastate.mt";

bool is_state(lua_State * L, int idx) {
    return testudata(L, idx, state_mt);
}

script_state & to_state(lua_State * L, int idx) {
    return *static_cast<script_state*>(luaL_checkudata(L, idx, state_mt));
}

int push_state(lua_State * L, script_state const & s) {
    void * mem = lua_newuserdata(L, sizeof(script_state));
    new (mem) script_state(s);
    luaL_getmetatable(L, state_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_state(lua_State * L) {
    script_state r;
    return push_state(L, r);
}

static int state_gc(lua_State * L) {
    to_state(L, 1).~script_state();
    return 0;
}

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
        switch (lua_type(src, i)) {
        case LUA_TNUMBER:   lua_pushnumber(tgt, lua_tonumber(src, i)); break;
        case LUA_TSTRING:   lua_pushstring(tgt, lua_tostring(src, i)); break;
        case LUA_TNIL:      lua_pushnil(tgt); break;
        case LUA_TBOOLEAN:  lua_pushboolean(tgt, lua_toboolean(src, i)); break;
        case LUA_TFUNCTION: {
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
            break;
        }
        case LUA_TUSERDATA:
            if (lua_migrate_fn f = get_migrate_fn(src, i)) {
                f(src, i, tgt);
            } else {
                throw exception("unsupported value type for inter-State call");
            }
            break;
        default:
            throw exception("unsupported value type for inter-State call");
        }
    }
}

int state_dostring(lua_State * L) {
    return to_state(L, 1).apply([&](lua_State * S) {
            char const * script = luaL_checkstring(L, 2);
            int first           = 3;
            int last            = lua_gettop(L);
            int sz_before = lua_gettop(S);
            int status = luaL_loadstring(S, script);
            if (status)
                throw script_exception(lua_tostring(S, -1));

            copy_values(L, first, last, S);

            pcall(S, first > last ? 0 : last - first + 1, LUA_MULTRET, 0);

            int sz_after = lua_gettop(S);

            if (sz_after > sz_before) {
                copy_values(S, sz_before + 1, sz_after, L);
                lua_pop(S, sz_after - sz_before);
            }
            return sz_after - sz_before;
        });
}

int state_set_global(lua_State * L) {
    to_state(L, 1).apply([=](lua_State * S) {
            char const * name = luaL_checkstring(L, 2);
            copy_values(L, 3, 3, S);
            lua_setglobal(S, name);
        });
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

    SET_GLOBAL_FUN(mk_state,   "State");
    SET_GLOBAL_FUN(state_pred, "is_State");
}

// TODO(Leo): allow the user to change it?
#define SMALL_DELAY 10 // in ms
std::chrono::milliseconds g_small_delay(SMALL_DELAY);

/**
   \brief Channel for communicating with thread objects in the Lua API
*/
class data_channel {
    // We use a lua_State to implement the channel. This is quite hackish,
    // but it is a convenient storage for Lua objects sent from one state to
    // another.
    script_state            m_channel;
    int                     m_ini;
    std::mutex              m_mutex;
    std::condition_variable m_cv;
public:
    data_channel() {
        lua_State * channel = m_channel.m_ptr->m_state;
        m_ini = lua_gettop(channel);
    }

    /**
       \brief Copy elements from positions [first, last] from src stack
       to the channel.
    */
    void write(lua_State * src, int first, int last) {
        // write the object on the top of the stack of src to the table
        // on m_channel.
        if (last < first)
            return;
        std::lock_guard<std::mutex> lock(m_mutex);
        lua_State * channel = m_channel.m_ptr->m_state;
        bool was_empty = lua_gettop(channel) == m_ini;
        copy_values(src, first, last, channel);
        if (was_empty)
            m_cv.notify_one();
    }

    /**
       \brief Retrieve one element from the channel. It will block
       the execution of \c tgt if the channel is empty.
    */
    int read(lua_State * tgt, int i) {
        std::unique_lock<std::mutex> lock(m_mutex);
        lua_State * channel = m_channel.m_ptr->m_state;
        if (i > 0) {
            // i is the position of the timeout argument
            std::chrono::milliseconds dura(luaL_checkinteger(tgt, i));
            if (lua_gettop(channel) == m_ini)
                m_cv.wait_for(lock, dura);
            if (lua_gettop(channel) == m_ini) {
                // timeout...
                lua_pushboolean(tgt, false);
                lua_pushnil(tgt);
                return 2;
            } else {
                lua_pushboolean(tgt, true);
                copy_values(channel, m_ini + 1, m_ini + 1, tgt);
                lua_remove(channel, m_ini + 1);
                return 2;
            }
        } else {
            while (lua_gettop(channel) == m_ini) {
                check_interrupted();
                m_cv.wait_for(lock, g_small_delay);
            }
            copy_values(channel, m_ini + 1, m_ini + 1, tgt);
            lua_remove(channel, m_ini + 1);
            return 1;
        }
    }
};

/**
   \brief We want the channels to be lazily created.
*/
class data_channel_ref {
    std::unique_ptr<data_channel> m_channel;
    std::mutex                    m_mutex;
public:
    data_channel & get() {
        std::lock_guard<std::mutex> lock(m_mutex);
        if (!m_channel)
            m_channel.reset(new data_channel());
        lean_assert(m_channel);
        return *m_channel;
    }
};

data_channel_ref g_in_channel;
data_channel_ref g_out_channel;

int channel_read(lua_State * L) {
    return g_in_channel.get().read(L, lua_gettop(L));
}

int channel_write(lua_State * L) {
    g_out_channel.get().write(L, 1, lua_gettop(L));
    return 0;
}

class leanlua_thread {
    script_state                    m_state;
    int                             m_sz_before;
    std::unique_ptr<exception>      m_exception;
    std::atomic<data_channel_ref *> m_in_channel_addr;
    std::atomic<data_channel_ref *> m_out_channel_addr;
    interruptible_thread            m_thread;
public:
    leanlua_thread(script_state const & st, int sz_before, int num_args):
        m_state(st),
        m_sz_before(sz_before),
        m_in_channel_addr(0),
        m_out_channel_addr(0),
        m_thread([=]() {
                m_in_channel_addr.store(&g_in_channel);
                m_out_channel_addr.store(&g_out_channel);
                m_state.apply([&](lua_State * S) {
                        int result = lua_pcall(S, num_args, LUA_MULTRET, 0);
                        if (result) {
                            if (is_exception(S, -1))
                                m_exception.reset(to_exception(S, -1).clone());
                            else
                                m_exception.reset(new script_exception(lua_tostring(S, -1)));
                        }
                    });
            }) {
    }

    ~leanlua_thread() {
        if (m_thread.joinable())
            m_thread.join();
    }

    int wait(lua_State * src) {
        m_thread.join();
        if (m_exception)
            m_exception->rethrow();
        return m_state.apply([&](lua_State * S) {
                int sz_after = lua_gettop(S);
                if (sz_after > m_sz_before) {
                    copy_values(S, m_sz_before + 1, sz_after, src);
                    lua_pop(S, sz_after - m_sz_before);
                }
                return sz_after - m_sz_before;
            });
    }

    void request_interrupt() {
        m_thread.request_interrupt();
    }

    void write(lua_State * src, int first, int last) {
        while (!m_in_channel_addr) {
            check_interrupted();
            std::this_thread::sleep_for(g_small_delay);
        }
        data_channel & in = m_in_channel_addr.load()->get();
        in.write(src, first, last);
    }

    int read(lua_State * src) {
        if (!m_out_channel_addr) {
            check_interrupted();
            std::this_thread::sleep_for(g_small_delay);
        }
        data_channel & out = m_out_channel_addr.load()->get();
        int nargs = lua_gettop(src);
        return out.read(src, nargs == 1 ? 0 : 2);
    }

    bool started() {
        return m_in_channel_addr && m_out_channel_addr;
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
    check_threadsafe();
    script_state & st   = to_state(L, 1);
    char const * script = luaL_checkstring(L, 2);
    int first           = 3;
    int last            = lua_gettop(L);
    int nargs           = first > last ? 0 : last - first + 1;
    int sz_before;
    st.apply([&](lua_State * S) {
            sz_before = lua_gettop(S);
            int result  = luaL_loadstring(S, script);
            if (result)
                throw script_exception(lua_tostring(S, -1));
            copy_values(L, first, last, S);
        });
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

static int thread_write(lua_State * L) {
    to_thread(L, 1).write(L, 2, lua_gettop(L));
    return 0;
}

static int thread_read(lua_State * L) {
    return to_thread(L, 1).read(L);
}

static int thread_interrupt(lua_State * L) {
    to_thread(L, 1).request_interrupt();
    return 0;
}

int thread_wait(lua_State * L) {
    return to_thread(L, 1).wait(L);
}

static const struct luaL_Reg thread_m[] = {
    {"__gc",      thread_gc},
    {"wait",      safe_function<thread_wait>},
    {"join",      safe_function<thread_wait>},
    {"interrupt", safe_function<thread_interrupt>},
    {"write",     safe_function<thread_write>},
    {"read",      safe_function<thread_read>},
    {0, 0}
};

static void open_thread(lua_State * L) {
    luaL_newmetatable(L, thread_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, thread_m, 0);

    SET_GLOBAL_FUN(mk_thread,   "thread");
    SET_GLOBAL_FUN(thread_pred, "is_thread");
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

static void open_interrupt(lua_State * L) {
    SET_GLOBAL_FUN(check_interrupted, "check_interrupted");
    SET_GLOBAL_FUN(sleep,             "sleep");
    SET_GLOBAL_FUN(yield,             "yield");
    SET_GLOBAL_FUN(channel_read,      "read");
    SET_GLOBAL_FUN(channel_write,     "write");
}

void open_extra(lua_State * L) {
    open_state(L);
    open_thread(L);
    open_interrupt(L);
}
}
