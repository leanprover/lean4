/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <library/sorry.h>
#include "library/scope_pos_info_provider.h"
#include "library/tactic/elaborator_exception.h"

namespace lean {
format failed_to_synthesize_placeholder_exception::pp() const {
    return m_fmt + line() + format("context:") + line() + m_state.pp();
}

optional<pos_info> nested_elaborator_exception::get_pos() const {
    try {
        std::rethrow_exception(m_exception);
    } catch (elaborator_exception & ex) {
        if (auto r = ex.get_pos())
            return r;
    } catch (...) {
    }
    return m_pos;
}

format nested_elaborator_exception::pp() const {
    format r;
    try {
        std::rethrow_exception(m_exception);
    } catch (nested_elaborator_exception & ex) {
        r = ex.pp();
    } catch (elaborator_exception & ex) {
        r = ex.pp();
        r += line() + format("Additional information:");
    } catch (...) {
    }
    pos_info_provider * pip = get_pos_info_provider();
    r += line();
    if (pip) {
        r += format(pip->get_file_name()) + format(":");
        if (m_pos) {
            r += format(m_pos->first) + format(":") + format(m_pos->second) + format(":");
        }
        r += space();
    }
    r += format("context: ") + m_fmt;
    return r;
}
}
