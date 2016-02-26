/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/flycheck.h"

namespace lean {
flycheck_scope::flycheck_scope(std::ostream & out, options const & o, char const * kind):
    m_out(out),
    m_flycheck(o.get_bool("flycheck", false)) {
    if (m_flycheck) m_out << "FLYCHECK_BEGIN " << kind << std::endl;
}
flycheck_scope::~flycheck_scope() {
    if (m_flycheck) m_out << "FLYCHECK_END" << std::endl;
}
}
