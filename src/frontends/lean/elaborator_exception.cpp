/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/scope_pos_info_provider.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
throwable * elaborator_exception::clone() const {
    return new elaborator_exception(m_expr, m_fmt);
}

throwable * nested_elaborator_exception::clone() const {
    return new nested_elaborator_exception(m_expr, m_fmt, m_exception);
}

optional<expr> nested_elaborator_exception::get_main_expr() const {
    if (auto r = m_exception->get_main_expr()) return r;
    else return m_expr;
}

format nested_elaborator_exception::pp() const {
    format r = m_exception->pp();
    if (dynamic_cast<nested_elaborator_exception*>(m_exception.get()) == nullptr) {
        r += line() + format("Additional information:");
    }
    pos_info_provider * pip = get_pos_info_provider();
    if (pip && m_expr) {
        if (auto p = pip->get_pos_info(*m_expr)) {
            r += line() + format(pip->get_file_name()) +
                colon() + format(p->first) + colon() + format(p->second) + colon() + space() + format("context: ") + m_fmt;
        } else {
            r += line() + format("context: ") + m_fmt;
        }
    } else {
        r += line() + format("context: ") + m_fmt;
    }
    return r;
}
}
