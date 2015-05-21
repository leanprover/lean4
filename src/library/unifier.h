/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <functional>
#include "util/lua.h"
#include "util/lazy_list.h"
#include "util/name_generator.h"
#include "util/sexpr/options.h"
#include "kernel/constraint.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"

namespace lean {
unsigned get_unifier_max_steps(options const & opts);
bool get_unifier_computation(options const & opts);

bool is_simple_meta(expr const & e);
expr mk_aux_metavar_for(name_generator & ngen, expr const & t);

enum class unify_status { Solved, Failed, Unsupported };
/**
    \brief Handle the easy-cases: first-order unification, higher-order patterns, identical terms, and terms without metavariables.

    This function assumes that all assigned metavariables have been substituted.
*/
unify_status unify_simple(substitution & s, expr const & lhs, expr const & rhs, justification const & j);
unify_status unify_simple(substitution & s, level const & lhs, level const & rhs, justification const & j);
unify_status unify_simple(substitution & s, constraint const & c);

enum class unifier_kind { Cheap, VeryConservative, Conservative, Liberal };

struct unifier_config {
    bool     m_use_exceptions;
    unsigned m_max_steps;
    bool     m_computation;
    bool     m_expensive_classes;
    // If m_discard is true, then constraints that cannot be solved are discarded (or incomplete methods are used)
    // If m_discard is false, unify returns the set of constraints that could not be handled.
    bool     m_discard;
    // If m_mind == Conservative, then the following restrictions are imposed:
    //     - All constants that are not at least marked as Quasireducible as treated as
    //       opaque.
    //     - Disables case-split on delta-delta constraints.
    //     - Disables reduction case-split on flex-rigid constraints.
    //
    // If m_kind == VeryConservative, then
    //     - More restrictive than Conservative,
    //     - All constants that are not at least marked as Reducible as treated as
    //       opaque.
    //
    // If m_kind == Cheap is true, then expensive case-analysis is not performed (e.g., delta).
    // It is more restrictive than VeryConservative
    //
    // Default is Liberal
    unifier_kind m_kind;
    // If m_pattern is true, then we restrict the number of cases splits on
    // flex-rigid constraints that are *not* in the higher-order pattern case.
    bool     m_pattern;
    // If m_ignore_context_check == true, then occurs-check is skipped.
    // Default is m_ignore_context_check == false
    bool     m_ignore_context_check;
    // If m_nonchronological is true, then nonchronological backtracking is used in the unifier.
    // Default is true
    bool     m_nonchronological;
    unifier_config(bool use_exceptions = false, bool discard = false);
    explicit unifier_config(options const & o, bool use_exceptions = false, bool discard = false);
};

/** \brief The unification procedures produce a lazy list of pair substitution + constraints that could not be solved. */
typedef lazy_list<pair<substitution, constraints>> unify_result_seq;

unify_result_seq unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator && ngen,
                       substitution const & s = substitution(), unifier_config const & c = unifier_config());
unify_result_seq unify(environment const & env, expr const & lhs, expr const & rhs, name_generator && ngen,
                       substitution const & s = substitution(), unifier_config const & c = unifier_config());

/**
    The unifier divides the constraints in 9 groups: Simple, Basic, FlexRigid, PluginDelayed, DelayedChoice, ClassInstance,
    Epilogue, FlexFlex, MaxDelayed

    1) Simple: constraints that never create case-splits. Example: pattern matching constraints (?M l_1 ... l_n) =?= t.
       The are not even inserted in the constraint priority queue.

    2) Basic: contains user choice constraints used to model coercions and overloaded constraints, and constraints
       that cannot be solved, and the unification plugin must be invoked.

    3) FlexRigid constraints (?M t_1 ... t_n) =?= t, where t_n is not an introduction application

    4) PluginDelayed: contraints delayed by the unifier_plugin. Examples: (elim ... (?m ...)) and (?m ... (intro ...)),
       where elim is an eliminator/recursor and intro is an introduction/constructor.
       This constraints are delayed because after ?m is assigned we may be able to reduce them.

    5) DelayedChoice: for delayed choice constraints (we use this group for the maximally delayed coercions constraints).

    6) ClassInstance: for delayed choice constraints (we use this group for class-instance).

    7) Epilogue: constraints that must be solved before FlexFlex are discarded/postponed.

    8) FlexFlex:  (?m1 ...) =?= (?m2 ...) we don't try to solve this constraint, we delay them and hope the other
       ones instantiate ?m1 or ?m2. If this kind of constraint is the next to be processed in the queue, then
       we simply discard it (or save it and return to the caller as residue).

    9) MaxDelayed: maximally delayed constraint group
*/
enum class cnstr_group { Basic = 0, FlexRigid, PluginDelayed, DelayedChoice, ClassInstance, Epilogue, FlexFlex, MaxDelayed };
inline unsigned to_delay_factor(cnstr_group g) { return static_cast<unsigned>(g); }

class unifier_exception : public exception {
    justification m_jst;
    substitution  m_subst;
public:
    unifier_exception(justification const & j, substitution const & s):exception("unifier exception"), m_jst(j), m_subst(s) {}
    virtual throwable * clone() const { return new unifier_exception(m_jst, m_subst); }
    virtual void rethrow() const { throw *this; }
    justification const & get_justification() const { return m_jst; }
    substitution const & get_substitution() const { return m_subst; }
};

void open_unifier(lua_State * L);

void initialize_unifier();
void finalize_unifier();
}
