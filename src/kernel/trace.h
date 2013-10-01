/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/debug.h"
#include "util/rc.h"
#include "util/buffer.h"
#include "util/sexpr/format.h"

namespace lean {
class trace;
/**
   \brief Base class used to represent trace objects.
   These objects are used to trace the execution of different engines in Lean.
   The traces may help users understanding why something did not work.
   The traces are particularly important for the elaborator.
*/
class trace_cell {
    MK_LEAN_RC();
    void dealloc() { delete this; }
public:
    virtual ~trace_cell() {}
    virtual format pp() const = 0;
    virtual void get_children(buffer<trace> & r) const = 0;
};

/**
   \brief Smart pointer for trace_cell's
*/
class trace {
    trace_cell * m_ptr;
    explicit trace(trace_cell * ptr):m_ptr(ptr) {}
public:
    trace():m_ptr(nullptr) {}
    trace(trace const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    trace(trace && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~trace() { if (m_ptr) m_ptr->dec_ref(); }

    operator bool() const { return m_ptr != nullptr; }

    trace_cell * raw() const { return m_ptr; }

    friend void swap(trace & a, trace & b) { std::swap(a.m_ptr, b.m_ptr); }

    trace & operator=(trace const & s) { LEAN_COPY_REF(trace, s); }
    trace & operator=(trace && s) { LEAN_MOVE_REF(trace, s); }
    format pp() const { lean_assert(m_ptr); return m_ptr->pp(); }
    void get_children(buffer<trace> & r) const { if (m_ptr) m_ptr->get_children(r); }
    bool has_children() const;
};

inline unsigned get_rc(trace const & t)    { return t.raw()->get_rc(); }
inline bool     is_shared(trace const & t) { return get_rc(t) > 1; }
inline format   pp(trace const & t)        { return t.pp(); }
inline void     get_children(trace const & t, buffer<trace> & r) {
    return t.get_children(r);
}
}
