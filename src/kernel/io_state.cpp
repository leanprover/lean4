/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/io_state.h"
#include "kernel/kernel_exception.h"

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
}
