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
    try {
        std::rethrow_exception(m_exception);
    } catch (ext_exception & ex) {
        return ex.get_pos();
    } catch (...) {
        return optional<pos_info>();
    }
}

format nested_exception::pp(formatter const & fmt) const {
    format r = m_pp_fn(fmt);
    r += line() + format("nested exception message:") + line();
    try {
        std::rethrow_exception(m_exception);
    } catch (ext_exception & ex) {
        r += ex.pp(fmt);
    } catch (std::exception & ex) {
        r += format(ex.what());
    } catch (...) {
    }
    return r;
}
}
