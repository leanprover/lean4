/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/state.h"

namespace lean {
namespace blast {
/** \brief Choice points are used different ways to proceed
    For example, given
       |- A \/ B
    we may proceed by trying to prove A or B. Each alternative
    is a different proof state. Actions my create choice points
    and add them to the choice point stack.
*/
class choice_point_cell {
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc() { delete this; }
public:
    choice_point_cell():m_rc(0) {}
    virtual ~choice_point_cell() {}
    /** \brief Update next proof state. This method may
        perform destructive updates, choice points are not shared
        objects.

        The next method result can be:
        1- Failed:    failure
        2- NewBranch: the current state has been updated, and it contains
           a new branch to be solved.
        3- Solved(pr): the current state has been updated, and its current
           branch has been closed by the next choice.
    */
    virtual action_result next() = 0;
};

/** \brief Smart pointer for choice points */
class choice_point {
    choice_point_cell * m_ptr;
public:
    choice_point():m_ptr(nullptr) {}
    choice_point(choice_point_cell * c):m_ptr(c) { m_ptr->inc_ref(); }
    choice_point(choice_point const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    choice_point(choice_point && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~choice_point() { if (m_ptr) m_ptr->dec_ref(); }
    choice_point & operator=(choice_point const & s) { LEAN_COPY_REF(s); }
    choice_point & operator=(choice_point && s) { LEAN_MOVE_REF(s); }

    action_result next() {
        lean_assert(m_ptr);
        return m_ptr->next();
    }
};

/** \brief Initialize thread local data-structures for storing choice points */
void init_choice_points();
/** \brief Add choice point to the top of the stack */
void push_choice_point(choice_point const & c);
inline void push_choice_point(choice_point_cell * cell) {
    push_choice_point(choice_point(cell));
}
/** \brief Keep executing choice points until one of them doesn't fail. */
action_result next_choice_point(unsigned base = 0);
/** \brief Return size of the choice point stack */
unsigned get_num_choice_points();
/** \brief Shrink the size of the choice point stack.
    \pre n <= get_num_choice_points */
void shrink_choice_points(unsigned n);
/** \brief Clear/remove all choice points */
void clear_choice_points();

class scope_choice_points {
    unsigned m_num_choices;
public:
    scope_choice_points():m_num_choices(get_num_choice_points()) {}
    ~scope_choice_points() { shrink_choice_points(m_num_choices); }
};
}}
