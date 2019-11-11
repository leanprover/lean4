/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/occurrences.h"

namespace lean {
bool occurrences::contains(unsigned occ_idx) const {
    switch (m_kind) {
    case All: return true;
    case Pos: return std::find(m_occs.begin(), m_occs.end(), occ_idx) != m_occs.end();
    case Neg: return std::find(m_occs.begin(), m_occs.end(), occ_idx) == m_occs.end();
    }
    lean_unreachable();
}
}
