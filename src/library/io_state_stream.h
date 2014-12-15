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
    environment const &  m_env;
    formatter            m_formatter;
    output_channel &     m_stream;
    io_state_stream(environment const & env, formatter const & fmt, output_channel & s):m_env(env), m_formatter(fmt), m_stream(s) {}
public:
    io_state_stream(environment const & env, io_state const & ios, bool regular = true):
        m_env(env), m_formatter(ios.get_formatter_factory()(env, ios.get_options())),
        m_stream(regular ? ios.get_regular_channel() : ios.get_diagnostic_channel()) {}
    std::ostream & get_stream() const { return m_stream.get_stream(); }
    void flush() { get_stream().flush(); }
    formatter const & get_formatter() const { return m_formatter; }
    options get_options() const { return m_formatter.get_options(); }
    environment const & get_environment() const { return m_env; }
    io_state_stream update_options(options const & o) const { return io_state_stream(m_env, m_formatter.update_options(o), m_stream); }
};

inline io_state_stream regular(environment const & env, io_state const & ios) { return io_state_stream(env, ios, true); }
inline io_state_stream diagnostic(environment const & env, io_state const & ios) { return io_state_stream(env, ios, false); }

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class kernel_exception;
class generic_exception;

io_state_stream const & operator<<(io_state_stream const & out, endl_class);
io_state_stream const & operator<<(io_state_stream const & out, expr const & e);
io_state_stream const & operator<<(io_state_stream const & out, kernel_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, generic_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, format const & f);
template<typename T> io_state_stream const & operator<<(io_state_stream const & out, T const & t) {
    out.get_stream() << t;
    return out;
}
}
