/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
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

static list<unsigned> to_list_unsigned(vm_obj const & occs) {
    return to_list<unsigned>(occs, [](vm_obj const & o) { return force_to_unsigned(o, 0); });
}

/*
inductive occurrences :=
| all
| pos : list nat → occurrences
| neg : list nat → occurrences  */
occurrences to_occurrences(vm_obj const & o) {
    switch (cidx(o)) {
    case 0: return occurrences();
    case 1: return occurrences(occurrences::Pos, to_list_unsigned(cfield(o, 0)));
    case 2: return occurrences(occurrences::Neg, to_list_unsigned(cfield(o, 0)));
    default: lean_unreachable();
    }
}

vm_obj occurrences::to_obj() const {
    switch (m_kind) {
    case All: return mk_vm_simple(0);
    case Pos: return mk_vm_constructor(1, ::lean::to_obj(m_occs));
    case Neg: return mk_vm_constructor(2, ::lean::to_obj(m_occs));
    }
    lean_unreachable();
}
}
