/*
  Copyright (c) 2017 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Sebastian Ullrich
*/
#include <string>
#include "util/parser_exception.h"

namespace lean {
char const * parser_exception::what() const noexcept {
    if (!m_what_buffer) {
        try {
            std::ostringstream s;
            s << m_fname << ":" << m_pos.first << ":" << m_pos.second << ": error: " << m_msg;
            const_cast<parser_exception*>(this)->m_what_buffer = s.str();
        } catch (std::exception & ex) {
            // failed to generate extended message
            return m_msg.c_str();
        }
    }
    return m_what_buffer->c_str();
}
}
