/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/scope_pos_info_provider.h"
#include "library/tactic/elaborator_exception.h"

namespace lean {
throwable * elaborator_exception::clone() const {
    return new elaborator_exception(m_pos, m_fmt);
}

format failed_to_synthesize_placeholder_exception::pp() const {
    return m_fmt + line() + format("context:") + line() + m_state.pp();
}

throwable * nested_elaborator_exception::clone() const {
    return new nested_elaborator_exception(m_pos, m_fmt, m_exception);
}

optional<pos_info> nested_elaborator_exception::get_pos() const {
    if (auto r = m_exception->get_pos()) return r;
    else return m_pos;
}

format nested_elaborator_exception::pp() const {
    format r = m_exception->pp();
    if (dynamic_cast<nested_elaborator_exception*>(m_exception.get()) == nullptr) {
        r += line() + format("Additional information:");
    }
    pos_info_provider * pip = get_pos_info_provider();
    r += line();
    if (pip) {
        r += format(pip->get_file_name()) + colon();
        if (m_pos) {
            r += format(m_pos->first) + colon() + format(m_pos->second) + colon();
        }
        r += space();
    }
    r += format("context: ") + m_fmt;
    return r;
}
}
