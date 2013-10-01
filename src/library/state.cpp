/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "library/state.h"

namespace lean {
state::state():
    m_formatter(mk_simple_formatter()),
    m_regular_channel(new stdout_channel()),
    m_diagnostic_channel(new stderr_channel()) {
}

state::state(options const & opts, formatter const & fmt):
    m_options(opts),
    m_formatter(fmt),
    m_regular_channel(new stdout_channel()),
    m_diagnostic_channel(new stderr_channel()) {
}

state::~state() {}

void state::set_regular_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_regular_channel = out;
}

void state::set_diagnostic_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_diagnostic_channel = out;
}

void state::set_options(options const & opts) {
    m_options = opts;
}

void state::set_formatter(formatter const & f) {
    m_formatter = f;
}

void regular::flush() {
    m_state.get_regular_channel().get_stream().flush();
}

void diagnostic::flush() {
    m_state.get_diagnostic_channel().get_stream().flush();
}

regular const & operator<<(regular const & out, endl_class) {
    out.m_state.get_regular_channel().get_stream() << std::endl;
    return out;
}

diagnostic const & operator<<(diagnostic const & out, endl_class) {
    out.m_state.get_diagnostic_channel().get_stream() << std::endl;
    return out;
}

regular const & operator<<(regular const & out, expr const & e) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(out.m_state.get_formatter()(e, opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, expr const & e) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(out.m_state.get_formatter()(e, opts), opts);
    return out;
}

regular const & operator<<(regular const & out, object const & obj) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(out.m_state.get_formatter()(obj, opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, object const & obj) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(out.m_state.get_formatter()(obj, opts), opts);
    return out;
}

regular const & operator<<(regular const & out, kernel_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_regular_channel().get_stream() << mk_pair(ex.pp(out.m_state.get_formatter(), opts), opts);
    return out;
}

diagnostic const & operator<<(diagnostic const & out, kernel_exception const & ex) {
    options const & opts = out.m_state.get_options();
    out.m_state.get_diagnostic_channel().get_stream() << mk_pair(ex.pp(out.m_state.get_formatter(), opts), opts);
    return out;
}
}
