/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/io_state.h"

namespace lean {
/**
   \brief Base class for \c regular and \c diagnostic wrapper classes.
*/
class io_state_stream {
protected:
    environment const & m_env;
    io_state const &    m_io_state;
public:
    io_state_stream(environment const & env, io_state const & s):m_env(env), m_io_state(s) {}
    virtual std::ostream & get_stream() const = 0;
    void flush() { get_stream().flush(); }
    formatter get_formatter() const { return m_io_state.get_formatter(); }
    options get_options() const { return m_io_state.get_options(); }
    environment const & get_environment() const { return m_env; }
};

/**
   \brief Wrapper for the io_state object that provides access to the
   io_state's regular channel
*/
class regular : public io_state_stream {
public:
    regular(environment const & env, io_state const & s):io_state_stream(env, s) {}
    std::ostream & get_stream() const { return m_io_state.get_regular_channel().get_stream(); }
};

/**
   \brief Wrapper for the io_state object that provides access to the
   io_state's diagnostic channel
*/
class diagnostic : public io_state_stream {
public:
    diagnostic(environment const & env, io_state const & s):io_state_stream(env, s) {}
    std::ostream & get_stream() const { return m_io_state.get_diagnostic_channel().get_stream(); }
};

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class kernel_exception;

io_state_stream const & operator<<(io_state_stream const & out, endl_class);
io_state_stream const & operator<<(io_state_stream const & out, expr const & e);
io_state_stream const & operator<<(io_state_stream const & out, kernel_exception const & ex);
template<typename T> io_state_stream const & operator<<(io_state_stream const & out, T const & t) {
    out.get_stream() << t;
    return out;
}
}
