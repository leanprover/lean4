/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
struct justification_idx_gen {
    unsigned       m_next_idx;
    list<unsigned> m_free_list;
public:
    justification_idx_gen():m_next_idx(0) {}
    void recycle(unsigned idx) {
        m_free_list = cons(idx, m_free_list);
    }
    unsigned next() {
        if (m_free_list) {
            unsigned r = head(m_free_list);
            m_free_list = tail(m_free_list);
            return r;
        } else {
            unsigned r = m_next_idx;
            m_next_idx++;
            return r;
        }
    }
};

MK_THREAD_LOCAL_GET_DEF(justification_idx_gen, get_justification_idx_gen)

justification_cell::justification_cell():m_rc(0) {
    m_idx = get_justification_idx_gen().next();
}

void justification_cell::dealloc() {
    get_justification_idx_gen().recycle(m_idx);
    delete this;
}

justification::justification():m_ptr(nullptr) {}
justification::justification(justification_cell & ptr):m_ptr(&ptr) { if (m_ptr) m_ptr->inc_ref(); }
justification::justification(justification const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
justification::justification(justification && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
justification::~justification() { if (m_ptr) m_ptr->dec_ref(); }
justification & justification::operator=(justification const & s) { LEAN_COPY_REF(s); }
justification & justification::operator=(justification && s) { LEAN_MOVE_REF(s); }
}}
