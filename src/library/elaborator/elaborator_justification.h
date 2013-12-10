/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "kernel/justification.h"
#include "kernel/unification_constraint.h"

namespace lean {
/**
   \brief Base class for justifying propagations and failures
*/
class propagation_justification : public justification_cell {
    unification_constraint m_constraint;
protected:
    /** \brief Auxiliary method used by pp_header to label a propagation step, subclasses must redefine it. */
    virtual char const * get_prop_name() const = 0;
public:
    propagation_justification(unification_constraint const & c);
    virtual ~propagation_justification();
    virtual void get_children(buffer<justification_cell*> & r) const;
    virtual optional<expr> get_main_expr() const;
    virtual format pp_header(formatter const &, options const &) const;
    unification_constraint const & get_constraint() const { return m_constraint; }
};

/**
   \brief Justification object used to mark that a particular unification constraint could not be solved.
*/
class unification_failure_justification : public propagation_justification {
protected:
    virtual char const * get_prop_name() const { return "Failed to solve"; }
public:
    unification_failure_justification(unification_constraint const & c):propagation_justification(c) {}
};

/**
   \brief Justification object created for justifying that a constraint that
   generated a case-split does not have a solution. Each case-split
   corresponds to a different way of solving the constraint.
*/
class unification_failure_by_cases_justification : public unification_failure_justification {
    std::vector<justification> m_cases; // why each case failed
public:
    unification_failure_by_cases_justification(unification_constraint const & c, unsigned num, justification const * cs);
    virtual ~unification_failure_by_cases_justification();
    virtual void get_children(buffer<justification_cell*> & r) const;
};

/**
   \brief Justification object used to justify a metavar assignment.
*/
class assignment_justification : public propagation_justification {
protected:
    virtual char const * get_prop_name() const { return "Assignment"; }
public:
    assignment_justification(unification_constraint const & c):propagation_justification(c) {}
};

/**
   \brief Justification object used to justify simple structural steps when processing unification
   constraints. For example, given the constraint

   <tt>ctx |- (f a) == (f b)</tt>

   where \c f is a variable, we must have

   <tt>ctx |- a == b</tt>

   The justification for the latter is a destruct justification based on the former.
*/
class destruct_justification : public propagation_justification {
protected:
    virtual char const * get_prop_name() const { return "Destruct/Decompose"; }
public:
    destruct_justification(unification_constraint const & c):propagation_justification(c) {}
};

/**
   \brief Justification object used to justify a normalization step such as.

   <tt>ctx |- (fun x : T, x) a == b</tt>
   ==>
   <tt>ctx |- a == b</tt>
*/
class normalize_justification : public propagation_justification {
protected:
    virtual char const * get_prop_name() const { return "Normalize"; }
public:
    normalize_justification(unification_constraint const & c):propagation_justification(c) {}
};

/**
   \brief Justification object used to justify an imitation step.
   An imitation step is used when solving constraints such as:

   <tt>ctx |- ?m[lift:s:n, ...] == Pi (x : A), B x</tt>

   In this case, ?m must be a Pi. We make progress, by adding the constraint
   <tt>ctx |- ?m == Pi (x : ?M1), (?M2 x)</tt>

   where ?M1 and ?M2 are fresh metavariables.
*/
class imitation_justification : public propagation_justification {
protected:
    virtual char const * get_prop_name() const { return "Imitation"; }
public:
    imitation_justification(unification_constraint const & c):propagation_justification(c) {}
};

/**
   \brief Justification object used to justify a new constraint obtained by substitution.
*/
class substitution_justification : public propagation_justification {
    justification                  m_assignment_justification;
protected:
    virtual char const * get_prop_name() const { return "Substitution"; }
public:
    substitution_justification(unification_constraint const & c, justification const & t);
    virtual ~substitution_justification();
    virtual void get_children(buffer<justification_cell*> & r) const;
};

/**
   \brief Justification object used to justify a new constraint obtained by multiple substitution.
*/
class multi_substitution_justification : public propagation_justification {
    std::vector<justification>    m_assignment_justifications;
protected:
    virtual char const * get_prop_name() const { return "Substitution"; }
public:
    multi_substitution_justification(unification_constraint const & c, unsigned num, justification const * ts);
    virtual ~multi_substitution_justification();
    virtual void get_children(buffer<justification_cell*> & r) const;
};

/**
   \brief Justification object used to justify a <tt>typeof(m) == t</tt> constraint generated when
   we assign a metavariable \c m.
*/
class typeof_mvar_justification : public justification_cell {
    context m_context;
    expr    m_mvar;
    expr    m_typeof_mvar;
    expr    m_type;
    justification   m_justification;
public:
    typeof_mvar_justification(context const & ctx, expr const & m, expr const & mt, expr const & t, justification const & tr);
    virtual ~typeof_mvar_justification();
    virtual format pp_header(formatter const &, options const &) const;
    virtual void get_children(buffer<justification_cell*> & r) const;
};

/**
    \brief Justification object used to justify that we are moving to the next solution.
*/
class next_solution_justification : public justification_cell {
    std::vector<justification> m_assumptions; // Set of assumptions used to derive last solution
public:
    next_solution_justification(unsigned num, justification const * as);
    virtual ~next_solution_justification();
    virtual format pp_header(formatter const &, options const &) const;
    virtual void get_children(buffer<justification_cell*> & r) const;
    virtual optional<expr> get_main_expr() const;
};
};
