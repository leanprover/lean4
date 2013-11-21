/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic.h"

namespace lean {
tactic_result::~tactic_result() {
}
void tactic_result::interrupt() {
    m_result = true;
}

tactic_cell::~tactic_cell() {
}

tactic & tactic::operator=(tactic const & s) {
    LEAN_COPY_REF(tactic, s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(tactic, s);
}
}
