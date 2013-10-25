/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <vector>
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/justification.h"

namespace lean {
/**
   \brief There are four kinds of unification constraints in Lean

   1-  ctx |- t == s                         t is (definitionally) equal to s
   2-  ctx |- t << s                         t is convertible to s (this is weaker than equality)
   3-  ctx |- max(t1, t2) == s               The maximum of t1 and t2 is equal to s
   4-  ctx |- ?m == t_1 Or ... Or ?m == t_k  The metavariable ?m is equal to t_1, ..., or t_k

   \remark The constraint <tt>ctx |- t == s</tt> implies that <tt>ctx |- t << s</tt>, but
   the converse is not true. Example: <tt>ctx |- Type 1 << Type 2</tt>, but
   we don't have <tt>ctx |- Type 1 == Type 2</tt>.

   \remark In the max constraint, \c t1 and \c t2 must be eventually unifiable with a Type term.
   For example, assume the constraint <tt>ctx |- max(?m1, Type 1) == ?m2</tt>. Now, suppose
   <tt>?m2</tt> is assigned to <tt>Type 1</tt>. Then, <tt>?m1</tt> can be assigned to <tt>Type 0</tt>
   or <tt>Type 1</tt>.
*/
enum class unification_constraint_kind { Eq, Convertible, Max, Choice };

/**
   \brief Base class for all Lean unification constraints.
*/
class unification_constraint_cell {
protected:
    unification_constraint_kind m_kind;
    context                     m_ctx;
    justification               m_justification; //!< justification for this constraint
    MK_LEAN_RC();
    void dealloc();
public:
    unification_constraint_cell(unification_constraint_kind k, context const & c, justification const & j);
    virtual ~unification_constraint_cell();
    unification_constraint_kind kind() const { return m_kind; }
    justification const & get_justification() const { return m_justification; }
    context const & get_context() const { return m_ctx; }
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const = 0;
    void set_justification(justification const & j) { lean_assert(!m_justification); m_justification = j; }
};

class unification_constraint {
private:
    unification_constraint_cell * m_ptr;
    explicit unification_constraint(unification_constraint_cell * ptr):m_ptr(ptr) {}
public:
    unification_constraint():m_ptr(nullptr) {}
    unification_constraint(unification_constraint const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    unification_constraint(unification_constraint && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~unification_constraint() { if (m_ptr) m_ptr->dec_ref(); }

    friend void swap(unification_constraint & a, unification_constraint & b) { std::swap(a.m_ptr, b.m_ptr); }

    unification_constraint & operator=(unification_constraint const & s) { LEAN_COPY_REF(unification_constraint, s); }
    unification_constraint & operator=(unification_constraint && s) { LEAN_MOVE_REF(unification_constraint, s); }

    unification_constraint_kind kind() const { return m_ptr->kind(); }
    unification_constraint_cell * raw() const { return m_ptr; }

    operator bool() const { return m_ptr != nullptr; }

    format pp(formatter const & fmt, options const & opts, pos_info_provider const * p = nullptr, bool include_justification = false) const {
        lean_assert(m_ptr);
        return m_ptr->pp(fmt, opts, p, include_justification);
    }

    justification const & get_justification() const { lean_assert(m_ptr); return m_ptr->get_justification(); }
    void set_justification(justification const & j) { lean_assert(!get_justification()); lean_assert(m_ptr); m_ptr->set_justification(j); }

    friend unification_constraint mk_eq_constraint(context const & c, expr const & lhs, expr const & rhs, justification const & j);
    friend unification_constraint mk_convertible_constraint(context const & c, expr const & from, expr const & to, justification const & j);
    friend unification_constraint mk_max_constraint(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, justification const & j);
    friend unification_constraint mk_choice_constraint(context const & c, expr const & mvar, unsigned num, expr const * choices, justification const & j);
};

/**
   \brief Unification constraint of the form <tt>ctx |- lhs == rhs</tt>
*/
class unification_constraint_eq : public unification_constraint_cell {
    expr m_lhs;
    expr m_rhs;
public:
    unification_constraint_eq(context const & c, expr const & lhs, expr const & rhs, justification const & j);
    virtual ~unification_constraint_eq();
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const;
};

/**
   \brief Unification constraint of the form <tt>ctx |- from << to</tt>.
   The meaning is \c from is convertible to \c to. Example: <tt>ctx |- Type 1 << Type 2</tt>.
   It is weaker than <tt>ctx |- from == rhs</tt>.
*/
class unification_constraint_convertible : public unification_constraint_cell {
    expr m_from;
    expr m_to;
public:
    unification_constraint_convertible(context const & c, expr const & from, expr const & to, justification const & j);
    virtual ~unification_constraint_convertible();
    expr const & get_from() const { return m_from; }
    expr const & get_to() const   { return m_to; }
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const;
};

/**
   \brief Unification constraint of the form <tt>ctx |- max(lhs1, lhs2) == rhs</tt>.
*/
class unification_constraint_max : public unification_constraint_cell {
    expr m_lhs1;
    expr m_lhs2;
    expr m_rhs;
public:
    unification_constraint_max(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, justification const & j);
    virtual ~unification_constraint_max();
    expr const & get_lhs1() const { return m_lhs1; }
    expr const & get_lhs2() const { return m_lhs2; }
    expr const & get_rhs() const  { return m_rhs; }
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const;
};

/**
   \brief Unification constraint of the form <tt>ctx |- mvar == choices[0] OR ... OR mvar == choices[size-1]</tt>.
*/
class unification_constraint_choice : public unification_constraint_cell {
    expr              m_mvar;
    std::vector<expr> m_choices;
public:
    unification_constraint_choice(context const & c, expr const & mvar, unsigned num, expr const * choices, justification const & j);
    virtual ~unification_constraint_choice();
    expr const & get_mvar() const               { return m_mvar; }
    unsigned     get_num_choices() const        { return m_choices.size(); }
    expr const & get_choice(unsigned idx) const { return m_choices[idx]; }
    std::vector<expr>::const_iterator begin_choices() const { return m_choices.begin(); }
    std::vector<expr>::const_iterator end_choices() const   { return m_choices.end(); }
    virtual format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const;
};

unification_constraint mk_eq_constraint(context const & c, expr const & lhs, expr const & rhs, justification const & j);
unification_constraint mk_convertible_constraint(context const & c, expr const & from, expr const & to, justification const & j);
unification_constraint mk_max_constraint(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, justification const & j);
unification_constraint mk_choice_constraint(context const & c, expr const & mvar, unsigned num, expr const * choices, justification const & j);
unification_constraint mk_choice_constraint(context const & c, expr const & mvar, std::initializer_list<expr> const & choices, justification const & j);

inline bool is_eq(unification_constraint const & c)          { return c.kind() == unification_constraint_kind::Eq; }
inline bool is_convertible(unification_constraint const & c) { return c.kind() == unification_constraint_kind::Convertible; }
inline bool is_max(unification_constraint const & c)         { return c.kind() == unification_constraint_kind::Max; }
inline bool is_choice(unification_constraint const & c)      { return c.kind() == unification_constraint_kind::Choice; }

inline unification_constraint_eq *          to_eq(unification_constraint const & c)          { lean_assert(is_eq(c)); return static_cast<unification_constraint_eq*>(c.raw()); }
inline unification_constraint_convertible * to_convertible(unification_constraint const & c) { lean_assert(is_convertible(c)); return static_cast<unification_constraint_convertible*>(c.raw()); }
inline unification_constraint_max *         to_max(unification_constraint const & c)         { lean_assert(is_max(c)); return static_cast<unification_constraint_max*>(c.raw()); }
inline unification_constraint_choice *      to_choice(unification_constraint const & c)      { lean_assert(is_choice(c)); return static_cast<unification_constraint_choice*>(c.raw()); }

inline context const & get_context(unification_constraint const & c) { return c.raw()->get_context(); }
inline justification   const & get_justification(unification_constraint const & c) { return c.raw()->get_justification(); }
inline expr const & eq_lhs(unification_constraint const & c) { return to_eq(c)->get_lhs(); }
inline expr const & eq_rhs(unification_constraint const & c) { return to_eq(c)->get_rhs(); }
inline expr const & convertible_from(unification_constraint const & c) { return to_convertible(c)->get_from(); }
inline expr const & convertible_to(unification_constraint const & c) { return to_convertible(c)->get_to(); }
inline expr const & max_lhs1(unification_constraint const & c) { return to_max(c)->get_lhs1(); }
inline expr const & max_lhs2(unification_constraint const & c) { return to_max(c)->get_lhs2(); }
inline expr const & max_rhs(unification_constraint const & c) { return to_max(c)->get_rhs(); }
inline expr const & choice_mvar(unification_constraint const & c) { return to_choice(c)->get_mvar(); }
inline unsigned     choice_size(unification_constraint const & c) { return to_choice(c)->get_num_choices(); }
inline expr const & choice_ith(unification_constraint const & c, unsigned i) { return to_choice(c)->get_choice(i); }
}
