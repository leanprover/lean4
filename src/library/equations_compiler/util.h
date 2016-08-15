/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** \brief Helper class for modifying/updating an equations-expression.

    \remark The equations macro is awkward to use since it is a leftover
    from the Lean2 equation compiler. The class tries to hide the problems
    with this data-structure. We cannot change the equations-macro
    until we remove the old equations compiler.

    TODO(Leo): as soon as we remove the legacy code from Lean2, this
    class will be much simpler. */
class equations_editor {
    expr                 m_src;
    buffer<expr>         m_fns;
    /* m_arity[i] contains the number of arguments for each equation lhs
       for m_fns[i].
       \remark m_arity.size() == m_fns.size().
       \remark The information stored in this field is ignore by repack. */
    buffer<unsigned>     m_arity;
    /* m_eqns[i] are the equations for m_fns[i].
       \remark m_eqs.size() == m_fns.size(). */
    buffer<buffer<expr>> m_eqs;
public:
    /** \brief Extract the data stored in the equations-expression \c e.
        \pre is_equations(e) */
    void unpack(expr const & e);
    /** \brief Re-build an equations-expression using the information
        stored at m_fns and m_eqs. */
    expr repack();

    unsigned get_num_fns() const { return m_fns.size(); }
    expr & get_fn(unsigned fidx) { return m_fns[fidx]; }
    expr const & get_fn(unsigned fidx) const { return m_fns[fidx]; }
    buffer<expr> & get_eqs_of(unsigned fidx) { return m_eqs[fidx]; }
    buffer<expr> const & get_eqs_of(unsigned fidx) const { return m_eqs[fidx]; }
    unsigned get_arity(unsigned fidx) const { return m_arity[fidx]; }
};

/** \brief Create a new equations object where all functions being defined are unary.
    The trick is to pack multiple arguments using a Sigma type. */
expr pack_equations_domain(type_context & ctx, expr const & e);
}
