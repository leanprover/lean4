/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "state.h"

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
    m_regular_channel = out;
}

void state::set_diagnostic_channel(std::shared_ptr<output_channel> const & out) {
    m_diagnostic_channel = out;
}

void state::set_options(options const & opts) {
    m_options = opts;
}

void state::set_formatter(formatter const & f) {
    m_formatter = f;
}
}
