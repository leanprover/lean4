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
class state {
    options                         m_options;
    formatter                       m_formatter;
    std::shared_ptr<output_channel> m_regular_channel;
    std::shared_ptr<output_channel> m_diagnostic_channel;
public:
    state();
    state(options const & opts, formatter const & fmt);
    ~state();

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
   \brief Wrapper for the state object that provides access to the
   state's regular channel
*/
struct regular {
    state const & m_state;
    regular(state const & s):m_state(s) {}
    void flush();
};

/**
   \brief Wrapper for the state object that provides access to the
   state's diagnostic channel
*/
struct diagnostic {
    state const & m_state;
    diagnostic(state const & s):m_state(s) {}
    void flush();
};

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class kernel_exception;

regular const &    operator<<(regular const & out,    endl_class);
diagnostic const & operator<<(diagnostic const & out, endl_class);
regular const &    operator<<(regular const & out,    expr const & e);
diagnostic const & operator<<(diagnostic const & out, expr const & e);
regular const &    operator<<(regular const & out,    object const & obj);
diagnostic const & operator<<(diagnostic const & out, object const & obj);
regular const &    operator<<(regular const & out,    kernel_exception const & ex);
diagnostic const & operator<<(diagnostic const & out, kernel_exception const & ex);

template<typename T>
inline regular const & operator<<(regular const & out, T const & t) {
    out.m_state.get_regular_channel().get_stream() << t;
    return out;
}

template<typename T>
inline diagnostic const & operator<<(diagnostic const & out, T const & t) {
    out.m_state.get_diagnostic_channel().get_stream() << t;
    return out;
}
}
