/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "library/type_context.h"
#include "library/reducible.h"

namespace lean {
/** \brief Type context for solving matching and simple unification problems.
    It only supports meta-variables created with the module idx_metavar.h.
    Internally, it stores the meta-variable assignments in an array.
    So, it is assuming the metavariables have small indices.

    The assignment and backtracking stack can be reset using the clear method.

    \remark By default, this object assumes that non-reducible constants are opaque.
    We can change that by providing a different reducible_behavior value when
    creating the object.

    \remark The default implementations for infer_local(e) and
    infer_metavar(e) just return mlocal_type(e). They must be
    redefined if we want to use this class in modules that store the type
    of local constants and meta-variables in a different place.

    \remark The local context is set using the method set_context from type_context.
*/
class tmp_type_context : public type_context {
    name_predicate                    m_opaque_pred;
    std::vector<optional<level>>      m_uassignment;
    std::vector<optional<expr>>       m_eassignment;
    enum class trail_kind { Level, Expr };
    std::vector<pair<trail_kind, unsigned>> m_trail; // undo stack
    struct scope {
        unsigned m_old_next_local_idx;
        unsigned m_uassignment_sz;
        unsigned m_eassignment_sz;
        unsigned m_trail_sz;
    };
    std::vector<scope>                m_scopes;
    void init(environment const & env, reducible_behavior b);
public:
    tmp_type_context(environment const & env, options const & o, reducible_behavior b = UnfoldReducible);
    tmp_type_context(environment const & env, options const & o,
                     tmp_local_generator & gen, reducible_behavior b = UnfoldReducible);
    virtual ~tmp_type_context();

    /** \brief Reset the state: backtracking stack, indices and assignment. */
    void clear();

    /** \remark The following methods are useful when indexed meta-variables have been created outside
        of this module.
        \pre This method should only be invoked if not meta-variable has been created.
        Use the method clear() to ensure this condition holds */
    void set_next_uvar_idx(unsigned next_idx);

    /** \remark The following methods are useful when indexed meta-variables have been created outside
        of this module.
        \pre This method should only be invoked if not meta-variable has been created.
        Use the method clear() to ensure this condition holds */
    void set_next_mvar_idx(unsigned next_idx);

    virtual bool is_extra_opaque(name const & n) const { return m_opaque_pred(n); }
    virtual bool is_uvar(level const & l) const;
    virtual bool is_mvar(expr const & e) const;
    virtual optional<level> get_assignment(level const & u) const;
    virtual optional<expr> get_assignment(expr const & m) const;
    virtual void update_assignment(level const & u, level const & v);
    virtual void update_assignment(expr const & m, expr const & v);

    virtual expr infer_local(expr const & e) const { return mlocal_type(e); }
    virtual expr infer_metavar(expr const & e) const { return mlocal_type(e); }

    virtual level mk_uvar();
    virtual expr mk_mvar(expr const &);

    virtual void push();
    virtual void pop();
    virtual void commit();

    bool is_uvar_assigned(unsigned idx) const {
        lean_assert(idx < m_uassignment.size());
        return static_cast<bool>(m_uassignment[idx]);
    }

    bool is_mvar_assigned(unsigned idx) const {
        lean_assert(idx < m_eassignment.size());
        return static_cast<bool>(m_eassignment[idx]);
    }
};
}
