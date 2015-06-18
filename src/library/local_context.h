/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "kernel/expr.h"

namespace lean {
/** \brief Auxiliary data-structure for storing the local context,
    and creating metavariables in the scope of the local context efficiently
*/
class local_context {
    list<expr>       m_ctx; // current local context: a list of local constants
    typedef std::tuple<name, expr, binder_info> local_decl;
    list<local_decl> m_ctx_abstracted; // m_ctx where elements have been abstracted
    static expr abstract_locals(expr const & e, list<expr> const & locals);
    // convert a local constant into a local_decl
    static local_decl to_local_decl(expr const & l, list<expr> const & ctx);
public:
    local_context();
    local_context(list<expr> const & ctx);

    void set_ctx(list<expr> const & ctx);

    /** \brief Given <tt>e[l_1, ..., l_n]</tt> and assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        then the result is
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), e[x_1, ... x_n])</tt>.
    */
    expr pi_abstract_context(expr e, tag g) const;

    /** \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return <tt>(f l_1 ... l_n)</tt>.
    */
    expr apply_context(expr const & f, tag g) const;

    /** \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return a fresh metavariable \c ?m with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        where \c ?u is a fresh universe metavariable.
    */
    expr mk_type_metavar(name_generator & ngen, tag g) const;

    /** \brief Assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return <tt>(?m l_1 ... l_n)</tt> where \c ?m is a fresh metavariable with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        and \c ?u is a fresh universe metavariable.

        \remark The type of the resulting expression is <tt>Type.{?u}</tt>
    */
    expr mk_type_meta(name_generator & ngen, tag g) const;

    /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        then the result is a fresh metavariable \c ?m with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), type[x_1, ... x_n])</tt>.
        If <tt>type</tt> is none, then the result is a fresh metavariable \c ?m1 with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), ?m2 x1 .... xn)</tt>,
        where ?m2 is another fresh metavariable with type
           <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
        and \c ?u is a fresh universe metavariable.

        \remark If \c suffix is not none, then it is appended to the (fresh) metavariable name.
    */
    expr mk_metavar(name_generator & ngen, optional<name> const & suffix, optional<expr> const & type, tag g) const;

    /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
           <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
        return (?m l_1 ... l_n), where ?m is a fresh metavariable
        created using \c mk_metavar.

        \see mk_metavar

        \remark If \c suffix is not none, then it is appended to the (fresh) metavariable name.
    */
    expr mk_meta(name_generator & ngen, optional<name> const & suffix, optional<expr> const & type, tag g) const;
    expr mk_meta(name_generator & ngen, optional<expr> const & type, tag g) const {
        return mk_meta(ngen, optional<name>(), type, g);
    }

    /** \brief Return context as a list */
    list<expr> const & get_data() const;

    void add_local(expr const & l);

    /** \brief Instantiate metavariables occurring this local context using \c s, and return updated local_context */
    local_context instantiate(substitution s) const;
};
}
