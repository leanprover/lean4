/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "library/print.h"
#include "library/io_state.h"

namespace lean {
static io_state * g_dummy_ios = nullptr;

void initialize_io_state() {
    g_dummy_ios = new io_state(mk_print_formatter_factory());
}

void finalize_io_state() {
    delete g_dummy_ios;
}

io_state const & get_dummy_ios() {
    return *g_dummy_ios;
}

io_state::io_state():io_state(mk_print_formatter_factory()) {}

io_state::io_state(formatter_factory const & fmtf):
    m_formatter_factory(fmtf),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}

io_state::io_state(options const & opts, formatter_factory const & fmtf):
    m_options(opts),
    m_formatter_factory(fmtf),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}
io_state::io_state(io_state const & ios, std::shared_ptr<output_channel> const & r, std::shared_ptr<output_channel> const & d):
    m_options(ios.m_options),
    m_formatter_factory(ios.m_formatter_factory),
    m_regular_channel(r),
    m_diagnostic_channel(d) {
}
io_state::io_state(io_state const & ios, options const & o):
    m_options(o),
    m_formatter_factory(ios.m_formatter_factory),
    m_regular_channel(ios.m_regular_channel),
    m_diagnostic_channel(ios.m_diagnostic_channel) {
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

void io_state::set_formatter_factory(formatter_factory const & f) {
    m_formatter_factory = f;
}
}
