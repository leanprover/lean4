/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "library/old_type_context.h"

namespace lean {

/** \brief (Legacy) implementation for the generic type_context class.
    It implements a simple meta-variable assignment.

    We use this class to implement the interface with the (old) elaborator. */
class legacy_type_context : public old_type_context {
    typedef rb_map<unsigned, level, unsigned_cmp> uassignment;
    typedef rb_map<unsigned, expr,  unsigned_cmp> eassignment;
    name_predicate            m_not_reducible_pred;

    struct assignment {
        uassignment m_uassignment;
        eassignment m_eassignment;
    };
    assignment                m_assignment;
    std::vector<assignment>   m_trail;
    unsigned                  m_next_uvar_idx;
    unsigned                  m_next_mvar_idx;

   /** \brief When m_ignore_if_zero is true, the following type-class resolution problem fails
       Given (A : Type{?u}), where ?u is a universe meta-variable created by an external module,

       ?Inst : subsingleton.{?u} A := subsingleton_prop ?M

       This case generates the unification problem

       subsingleton.{?u} A =?= subsingleton.{0} ?M

       which can be solved by assigning (?u := 0) and (?M := A)
       when the hack is enabled, the is_def_eq method in the type class module fails at the subproblem:

           ?u =?= 0

       That is, when the hack is on, type-class resolution cannot succeed by instantiating an external universe
       meta-variable with 0.
   */
    bool                      m_ignore_if_zero;

    unsigned uvar_idx(level const & l) const;
    unsigned mvar_idx(expr const & m) const;

public:
    legacy_type_context(environment const & env, options const & o,
                           list<expr> const & insts = list<expr>(), bool multiple_instances = false);
    virtual ~legacy_type_context();
    virtual bool is_extra_opaque(name const & n) const { return m_not_reducible_pred(n); }
    virtual bool ignore_universe_def_eq(level const & l1, level const & l2) const;
    virtual bool is_uvar(level const & l) const;
    virtual bool is_mvar(expr const & e) const;
    virtual optional<level> get_assignment(level const & u) const;
    virtual optional<expr> get_assignment(expr const & m) const;
    virtual void update_assignment(level const & u, level const & v);
    virtual void update_assignment(expr const & m, expr const & v);
    virtual level mk_uvar();
    virtual expr mk_mvar(expr const &);
    virtual expr infer_local(expr const & e) const { return mlocal_type(e); }
    virtual expr infer_metavar(expr const & e) const { return mlocal_type(e); }
    virtual void push_core() { m_trail.push_back(m_assignment); }
    virtual void pop_core() { lean_assert(!m_trail.empty()); m_assignment = m_trail.back(); m_trail.pop_back(); }
    virtual unsigned get_num_check_points() const { return m_trail.size(); }
    virtual void commit() { lean_assert(!m_trail.empty()); m_trail.pop_back(); }
    virtual optional<expr> mk_subsingleton_instance(expr const & type);
    virtual bool validate_assignment_types(expr const & m, expr const & v);
    // TODO(REMOVE)
    bool & get_ignore_if_zero() { return m_ignore_if_zero; }
};

void initialize_legacy_type_context();
void finalize_legacy_type_context();
}
