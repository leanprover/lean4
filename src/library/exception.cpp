/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/exception.h"

namespace lean {
static pp_fn mk_pp_fn(char const * msg) {
    std::string msg_str = msg;
    return [=](formatter const &) { return format(msg_str); }; // NOLINT
}

generic_exception::generic_exception(optional<expr> const & m, char const * msg):
    generic_exception(msg, m, mk_pp_fn(msg)) {}

optional<pos_info> nested_exception::get_pos() const {
    if (m_pos)
        return m_pos;
    else if (ext_exception * ex = dynamic_cast<ext_exception *>(m_exception.get()))
        return ex->get_pos();
    else
        return {};
}

format nested_exception::pp(formatter const & fmt) const {
    format r = m_pp_fn(fmt);
    r += line() + format("nested exception message:") + line();
    if (ext_exception * ex = dynamic_cast<ext_exception *>(m_exception.get())) {
        r += ex->pp(fmt);
    } else {
        r += format(m_exception->what());
    }
    return r;
}

throwable * nested_exception::clone() const {
    return new nested_exception(m_pos, m_pp_fn, *m_exception);
}
}
