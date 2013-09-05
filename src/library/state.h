/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "output_channel.h"
#include "formatter.h"
#include "options.h"

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
    void set_interrupt(bool flag) { m_formatter.set_interrupt(flag); }
};

struct regular {
    state const & m_state;
    regular(state const & s):m_state(s) {}
    void flush() { m_state.get_regular_channel().get_stream().flush(); }
};

struct diagnostic {
    state const & m_state;
    diagnostic(state const & s):m_state(s) {}
    void flush() { m_state.get_diagnostic_channel().get_stream().flush(); }
};

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;
inline regular const & operator<<(regular const & out, endl_class) {
    out.m_state.get_regular_channel().get_stream() << std::endl;
    return out;
}
inline diagnostic const & operator<<(diagnostic const & out, endl_class) {
    out.m_state.get_diagnostic_channel().get_stream() << std::endl;
    return out;
}

inline regular const & operator<<(regular const & out, expr const & e) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(out.m_state.get_formatter()(e, opts), opts);
    return out;
}

inline diagnostic const & operator<<(diagnostic const & out, expr const & e) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(out.m_state.get_formatter()(e, opts), opts);
    return out;
}

inline regular const & operator<<(regular const & out, object const & obj) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(out.m_state.get_formatter()(obj, opts), opts);
    return out;
}

inline diagnostic const & operator<<(diagnostic const & out, object const & obj) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(out.m_state.get_formatter()(obj, opts), opts);
    return out;
}

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
