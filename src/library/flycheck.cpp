/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/flycheck.h"

namespace lean {
flycheck_scope::flycheck_scope(io_state_stream const & ios, char const * kind):
    m_ios(ios),
    m_flycheck(m_ios.get_options().get_bool("flycheck", false)) {
    if (m_flycheck) m_ios << "FLYCHECK_BEGIN " << kind << endl;
}
flycheck_scope::~flycheck_scope() {
    if (m_flycheck) m_ios << "FLYCHECK_END" << endl;
}
}
