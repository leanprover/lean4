/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "kernel/ext_exception.h"
#include "kernel/abstract_type_context.h"
#include "library/exception.h"
#include "library/io_state.h"

namespace lean {
/** \brief Base class for \c regular and \c diagnostic wrapper classes. */
class io_state_stream {
protected:
    environment                     m_env;
    formatter                       m_formatter;
    std::shared_ptr<output_channel> m_stream;
public:
    io_state_stream(environment const & env, formatter const & fmt, std::shared_ptr<output_channel> const & s):
        m_env(env), m_formatter(fmt), m_stream(s) {}
    io_state_stream(environment const & env, io_state const & ios, abstract_type_context & ctx, std::shared_ptr<output_channel> const & stream):
        m_env(env), m_formatter(ios.get_formatter_factory()(env, ios.get_options(), ctx)),
        m_stream(stream) {}
    io_state_stream(environment const & env, io_state const & ios, abstract_type_context & ctx, bool regular = true):
        io_state_stream(env, ios, ctx, regular ? ios.get_regular_channel_ptr() : ios.get_diagnostic_channel_ptr()) {}
    std::ostream & get_stream() const { return m_stream->get_stream(); }
    std::shared_ptr<output_channel> get_channel() const { return m_stream; }
    void flush() { get_stream().flush(); }
    formatter const & get_formatter() const { return m_formatter; }
    options get_options() const { return m_formatter.get_options(); }
    environment const & get_environment() const { return m_env; }
    io_state_stream update_options(options const & o) const { return io_state_stream(m_env, m_formatter.update_options(o), m_stream); }
};

inline io_state_stream regular(environment const & env, io_state const & ios, abstract_type_context & ctx) {
    return io_state_stream(env, ios, ctx, true);
}
inline io_state_stream diagnostic(environment const & env, io_state const & ios, abstract_type_context & ctx) {
    return io_state_stream(env, ios, ctx, false);
}

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class ext_exception;

io_state_stream const & operator<<(io_state_stream const & out, endl_class);
io_state_stream const & operator<<(io_state_stream const & out, option_kind k);
io_state_stream const & operator<<(io_state_stream const & out, expr const & e);
io_state_stream const & operator<<(io_state_stream const & out, level const & l);
io_state_stream const & operator<<(io_state_stream const & out, ext_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, formatted_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, format const & f);
template<typename T> io_state_stream const & display(io_state_stream const & out, T const & t) {
    out.get_stream() << t;
    return out;
}
struct display_profiling_time;
io_state_stream const & operator<<(io_state_stream const & out, display_profiling_time const &);
inline io_state_stream const & operator<<(io_state_stream const & out, char const * d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, name const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, unsigned d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, std::string const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, options const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, pair<format const &, options const &> const & d) { return display(out, d); }
}
