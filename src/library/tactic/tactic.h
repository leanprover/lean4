/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/lazy_list.h"
#include "library/tactic/proof_state.h"

namespace lean {
class tactic_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    virtual ~tactic_cell() {}
    virtual lazy_list<proof_state> operator()(proof_state const & p) const = 0;
};

class tactic {
protected:
    tactic_cell * m_ptr;
public:
    explicit tactic(tactic_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~tactic() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(tactic & a, tactic & b) { std::swap(a.m_ptr, b.m_ptr); }
    tactic & operator=(tactic const & s) { LEAN_COPY_REF(tactic, s); }
    tactic & operator=(tactic && s) { LEAN_MOVE_REF(tactic, s); }

    lazy_list<proof_state> operator()(proof_state const & p) const { return m_ptr->operator()(p); }
};
}

