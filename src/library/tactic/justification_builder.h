/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/name.h"
#include "util/rc.h"
#include "kernel/expr.h"
#include "kernel/justification.h"
#include "library/tactic/assignment.h"

namespace lean {
class justification_builder_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    virtual ~justification_builder_cell() {}
    virtual justification operator()(name const & n, justification const & j, assignment const & a) const = 0;
};

class justification_builder {
protected:
    justification_builder_cell * m_ptr;
public:
    explicit justification_builder(justification_builder_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
    justification_builder(justification_builder const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    justification_builder(justification_builder && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~justification_builder() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(justification_builder & a, justification_builder & b) { std::swap(a.m_ptr, b.m_ptr); }
    justification_builder & operator=(justification_builder const & s) { LEAN_COPY_REF(justification_builder, s); }
    justification_builder & operator=(justification_builder && s) { LEAN_MOVE_REF(justification_builder, s); }

    justification operator()(name const & n, justification const & j, assignment const & a) const { return m_ptr->operator()(n, j, a); }
};
}
