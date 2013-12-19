/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/output_channel.h"
#include "util/sexpr/options.h"
#include "kernel/formatter.h"

namespace lean {
/**
   \brief State provided to internal lean procedures that need to:
   1- Access user defined options
   2- Produce verbosity messages
   3- Output results
   4- Produce formatted output
*/
class io_state {
    options                         m_options;
    formatter                       m_formatter;
    std::shared_ptr<output_channel> m_regular_channel;
    std::shared_ptr<output_channel> m_diagnostic_channel;
public:
    io_state();
    io_state(options const & opts, formatter const & fmt);
    ~io_state();

    options get_options() const { return m_options; }
    formatter get_formatter() const { return m_formatter; }
    output_channel & get_regular_channel() const { return *m_regular_channel; }
    output_channel & get_diagnostic_channel() const { return *m_diagnostic_channel; }

    void set_regular_channel(std::shared_ptr<output_channel> const & out);
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out);
    void set_options(options const & opts);
    void set_formatter(formatter const & f);
    template<typename T> void set_option(name const & n, T const & v) {
        set_options(get_options().update(n, v));
    }
};

/**
   \brief Base class for \c regular and \c diagnostic wrapper classes.
*/
class io_state_stream {
protected:
    io_state const & m_io_state;
public:
    io_state_stream(io_state const & s):m_io_state(s) {}
    virtual std::ostream & get_stream() const = 0;
    void flush() { get_stream().flush(); }
    formatter get_formatter() const { return m_io_state.get_formatter(); }
    options get_options() const { return m_io_state.get_options(); }
};

/**
   \brief Wrapper for the io_state object that provides access to the
   io_state's regular channel
*/
class regular : public io_state_stream {
public:
    regular(io_state const & s):io_state_stream(s) {}
    std::ostream & get_stream() const { return m_io_state.get_regular_channel().get_stream(); }
};

/**
   \brief Wrapper for the io_state object that provides access to the
   io_state's diagnostic channel
*/
class diagnostic : public io_state_stream {
public:
    diagnostic(io_state const & s):io_state_stream(s) {}
    std::ostream & get_stream() const { return m_io_state.get_diagnostic_channel().get_stream(); }
};

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class kernel_exception;

io_state_stream const & operator<<(io_state_stream const & out, endl_class);
io_state_stream const & operator<<(io_state_stream const & out, expr const & e);
io_state_stream const & operator<<(io_state_stream const & out, object const & obj);
io_state_stream const & operator<<(io_state_stream const & out, environment const & env);
io_state_stream const & operator<<(io_state_stream const & out, kernel_exception const & ex);
template<typename T> io_state_stream const & operator<<(io_state_stream const & out, T const & t) {
    out.get_stream() << t;
    return out;
}

UDATA_DEFS(io_state)
/**
   \brief Auxiliary class for temporarily setting the Lua registry of a Lua state
   with a Lean io_state object.
*/
class set_io_state {
    lua_State * m_state;
    io_state *  m_prev;
    options     m_prev_options;
public:
    set_io_state(lua_State * L, io_state & st);
    ~set_io_state();
};
/**
   \brief Return the Lean state object associated with the given Lua state.
   Return nullptr is there is none.
*/
io_state * get_io_state(lua_State * L);
void open_io_state(lua_State * L);
}
