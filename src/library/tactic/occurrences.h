/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
class occurrences {
public:
    enum kind { All, Pos, Neg };
private:
    kind           m_kind;
    list<unsigned> m_occs;
public:
    occurrences():m_kind(All) {}
    occurrences(kind k, list<unsigned> const & occs):m_kind(k), m_occs(occs) {}
    bool is_all() const { return m_kind == All; }
    bool is_except() const { return m_kind == Neg; }
    /** \brief Return true iff this occurrences object contains the given occurrences index. */
    bool contains(unsigned occ_idx) const;

    bool operator==(occurrences const & o) const { return m_kind == o.m_kind && m_occs == o.m_occs; }
    bool operator!=(occurrences const & o) const { return !operator==(o); }

    vm_obj to_obj() const;
};

occurrences to_occurrences(vm_obj const &);
inline vm_obj to_obj(occurrences const & occs) { return occs.to_obj(); }
}
