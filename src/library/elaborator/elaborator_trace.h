/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "kernel/trace.h"
#include "kernel/unification_constraint.h"

namespace lean {
/**
   \brief Base class for trace objects used to justify case-splits.
*/
class assumption_trace : public trace_cell {
    unsigned m_idx;
public:
    assumption_trace(unsigned idx);
    virtual void get_children(buffer<trace_cell*> &) const;
    virtual expr const & get_main_expr() const;
    virtual format pp_header(formatter const &, options const &) const;
};

/**
   \brief Base class for justifying propagations and failures
*/
class propagation_trace : public trace_cell {
    unification_constraint m_constraint;
protected:
    /** \brief Auxiliary method used by pp_header to label a propagation step, subclasses must redefine it. */
    virtual char const * get_prop_name() const = 0;
public:
    propagation_trace(unification_constraint const & c);
    virtual ~propagation_trace();
    virtual void get_children(buffer<trace_cell*> & r) const;
    virtual expr const & get_main_expr() const;
    virtual format pp_header(formatter const &, options const &) const;
    unification_constraint const & get_constraint() const { return m_constraint; }
};

/**
   \brief Trace object used to mark that a particular unification constraint could not be solved.
*/
class unification_failure_trace : public propagation_trace {
protected:
    virtual char const * get_prop_name() const { return "Failed to solve"; }
public:
    unification_failure_trace(unification_constraint const & c):propagation_trace(c) {}
};

/**
   \brief Trace object created for justifying that a constraint that
   generated a case-split does not have a solution. Each case-split
   corresponds to a different way of solving the constraint.
*/
class unification_failure_by_cases_trace : public unification_failure_trace {
    std::vector<trace> m_cases; // why each case failed
public:
    unification_failure_by_cases_trace(unification_constraint const & c, unsigned num, trace const * cs);
    virtual ~unification_failure_by_cases_trace();
    virtual void get_children(buffer<trace_cell*> & r) const;
};

/**
   \brief Trace object used to justify a metavar assignment.
*/
class assignment_trace : public propagation_trace {
protected:
    virtual char const * get_prop_name() const { return "Assignment"; }
public:
    assignment_trace(unification_constraint const & c):propagation_trace(c) {}
};

/**
   \brief Trace object used to justify simple structural steps when processing unification
   constraints. For example, given the constraint

   <tt>ctx |- (f a) == (f b)</tt>

   where \c f is a variable, we must have

   <tt>ctx |- a == b</tt>

   The justification for the latter is a destruct trace based on the former.
*/
class destruct_trace : public propagation_trace {
protected:
    virtual char const * get_prop_name() const { return "Destruct/Decompose"; }
public:
    destruct_trace(unification_constraint const & c):propagation_trace(c) {}
};

/**
   \brief Trace object used to justify a normalization step such as.

   <tt>ctx |- (fun x : T, x) a == b</tt>
   ==>
   <tt>ctx |- a == b</tt>
*/
class normalize_trace : public propagation_trace {
protected:
    virtual char const * get_prop_name() const { return "Normalize"; }
public:
    normalize_trace(unification_constraint const & c):propagation_trace(c) {}
};

/**
   \brief Trace object used to justify a new constraint obtained by substitution.
*/
class substitution_trace : public propagation_trace {
    trace                  m_assignment_trace;
protected:
    virtual char const * get_prop_name() const { return "Substitution"; }
public:
    substitution_trace(unification_constraint const & c, trace const & t);
    virtual ~substitution_trace();
    virtual void get_children(buffer<trace_cell*> & r) const;
};

/**
   \brief Trace object used to justify a new constraint obtained by multiple substitution.
*/
class multi_substitution_trace : public propagation_trace {
    std::vector<trace>    m_assignment_traces;
protected:
    virtual char const * get_prop_name() const { return "Substitution"; }
public:
    multi_substitution_trace(unification_constraint const & c, unsigned num, trace const * ts);
    virtual ~multi_substitution_trace();
    virtual void get_children(buffer<trace_cell*> & r) const;
};

/**
   \brief Base class for synthesis_failure_trace and synthesized_assignment_trace
*/
class synthesis_trace : public trace_cell {
    context            m_context;
    expr               m_mvar;
    expr               m_type;
    std::vector<trace> m_substitution_traces; // trace objects justifying the assignments used to instantiate \c m_type and \c m_context.
protected:
    virtual char const * get_label() const = 0;
public:
    synthesis_trace(context const & ctx, expr const & mvar, expr const & type, unsigned num, trace const * substs);
    virtual ~synthesis_trace();
    virtual format pp_header(formatter const &, options const &) const;
    virtual void get_children(buffer<trace_cell*> & r) const;
    virtual expr const & get_main_expr() const;
};

/**
   \brief Trace object for justifying why a synthesis step failed.
   A synthesis step is of the form

   <tt>ctx |- ?mvar : type</tt>

   Before invoking the synthesizer, the elaborator substitutes the
   metavariables in \c ctx and \c type with their corresponding assignments.
*/
class synthesis_failure_trace : public synthesis_trace {
    trace              m_trace;  // trace object produced by the synthesizer
protected:
    virtual char const * get_label() const;
public:
    synthesis_failure_trace(context const & ctx, expr const & mvar, expr const & type, trace const & tr, unsigned num, trace const * substs);
    virtual ~synthesis_failure_trace();
    virtual void get_children(buffer<trace_cell*> & r) const;
};

/**
   \brief Trace object used to justify a metavar assignment produced by a synthesizer.
*/
class synthesized_assignment_trace : public synthesis_trace {
protected:
    virtual char const * get_label() const;
public:
    synthesized_assignment_trace(context const & ctx, expr const & mvar, expr const & type, unsigned num, trace const * substs):
        synthesis_trace(ctx, mvar, type, num, substs) {
    }
};

/**
    \brief Trace object used to justify that we are moving to the next solution.
*/
class next_solution_trace : public trace_cell {
    std::vector<trace> m_assumptions; // Set of assumptions used to derive last solution
public:
    next_solution_trace(unsigned num, trace const * as);
    virtual ~next_solution_trace();
    virtual format pp_header(formatter const &, options const &) const;
    virtual void get_children(buffer<trace_cell*> & r) const;
    virtual expr const & get_main_expr() const;
};
};
