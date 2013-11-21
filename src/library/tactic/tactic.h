/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <memory>
#include <mutex>
#include "library/tactic/proof_state.h"

namespace lean {
typedef std::unique_ptr<proof_state> proof_state_ref;
class tactic_result;
typedef std::unique_ptr<tactic_result> tactic_result_ref;

class tactic_result {
    std::mutex    m_mutex;
    bool          m_result;
protected:
    template<typename F>
    void exclusive_update(F && f) {
        std::lock_guard<std::mutex> lock(m_mutex);
        f();
    }
    virtual void interrupt();
    void propagate_interrupt(tactic_result_ref & r) { if (r) r->interrupt(); }
public:
    tactic_result():m_result(false) {}
    bool interrupted() const { return m_result; }
    void request_interrupt();
    virtual ~tactic_result();
    virtual proof_state_ref next() = 0;
};

class tactic_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    virtual ~tactic_cell();
    virtual tactic_result_ref operator()(proof_state const & s) const = 0;
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
    tactic & operator=(tactic const & s);
    tactic & operator=(tactic && s);

    tactic_result_ref operator()(proof_state const & s) const { return m_ptr->operator()(s); }
};

tactic idtac();
tactic then(tactic const & t1, tactic const & t2);
}
