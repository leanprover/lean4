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
#include "kernel/expr.h"
#include "kernel/formatter.h"
#include "kernel/pos_info_provider.h"

namespace lean {
class justification;
/**
   \brief Base class used to represent justification objects.
   These objects are used to justification the execution of different engines in Lean.
   The justifications may help users understanding why something did not work.
   The justifications are particularly important for the elaborator.
*/
class justification_cell {
    MK_LEAN_RC();
    void dealloc() { delete this; }
protected:
    static void add_pos_info(format & r, optional<expr> const & e, pos_info_provider const * p);
public:
    justification_cell():m_rc(0) {}
    virtual ~justification_cell() {}
    virtual format pp_header(formatter const & fmt, options const & opts) const = 0;
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool display_children) const;
    virtual void get_children(buffer<justification_cell*> & r) const = 0;
    virtual optional<expr> get_main_expr() const { return none_expr(); }
    bool is_shared() const { return get_rc() > 1; }
};

/**
   \brief Base class for justification objects used to justify case-splits.
*/
class assumption_justification : public justification_cell {
    unsigned m_idx;
public:
    assumption_justification(unsigned idx);
    virtual void get_children(buffer<justification_cell*> &) const;
    virtual optional<expr> get_main_expr() const;
    virtual format pp_header(formatter const &, options const &) const;
};

/**
   \brief Smart pointer for justification_cell's
*/
class justification {
    justification_cell * m_ptr;
public:
    justification():m_ptr(nullptr) {}
    justification(justification_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    justification(justification const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    justification(justification && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~justification() { if (m_ptr) m_ptr->dec_ref(); }

    explicit operator bool() const { return m_ptr != nullptr; }

    justification_cell * raw() const { return m_ptr; }

    friend void swap(justification & a, justification & b) { std::swap(a.m_ptr, b.m_ptr); }

    justification & operator=(justification const & s) { LEAN_COPY_REF(s); }
    justification & operator=(justification && s) { LEAN_MOVE_REF(s); }
    format pp(formatter const & fmt, options const & opts, pos_info_provider const * p = nullptr, bool display_children = true) const {
        lean_assert(m_ptr);
        return m_ptr->pp(fmt, opts, p, display_children);
    }
    optional<expr> get_main_expr() const { return m_ptr ? m_ptr->get_main_expr() : none_expr(); }
    void get_children(buffer<justification_cell*> & r) const { if (m_ptr) m_ptr->get_children(r); }
    bool has_children() const;
};

inline justification mk_assumption_justification(unsigned idx) { return justification(new assumption_justification(idx)); }

/**
   \brief Return true iff \c t depends on \c d.
   That is \c t is a descendant of \c d.
*/
bool depends_on(justification const & t, justification const & d);

/** \brief Add \c t to \c r */
inline void push_back(buffer<justification_cell*> & r, justification const & t) {
    if (t) r.push_back(t.raw());
}

/** \brief Add justifications in the collection \c s into r. */
template<typename T>
void append(buffer<justification_cell*> & r, T const & s) {
    for (auto t : s)
        push_back(r, t);
}
}
