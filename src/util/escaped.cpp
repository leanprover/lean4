/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/escaped.h"

namespace lean {

char const * escaped::end() const {
    if (m_str == 0) return 0;
    char const * it = m_str;
    char const * e  = m_str;
    while (*it) {
        if (!m_trim_nl || *it != '\n') {
            ++it;
            e = it;
        } else {
            ++it;
        }
    }
    return e;
}

std::ostream & operator<<(std::ostream & out, escaped const & s) {
    char const * it = s.m_str;
    char const * e  = s.end();
    for (; it != e; ++it) {
        char c = *it;
        if (c == '"') {
            out << '\\';
        }
        out << c;
        if (c == '\n') {
            for (unsigned i = 0; i < s.m_indent; i++)
                out << " ";
        }
    }
    return out;
}

}
