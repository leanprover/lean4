/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/app_builder.h"
#include "library/fun_info_manager.h"

namespace lean {
enum class congr_arg_kind { Fixed, Eq, Cast };

class congr_lemma {
    expr                 m_type;
    expr                 m_proof;
    list<congr_arg_kind> m_arg_kinds;
public:
    congr_lemma(expr const & type, expr const & proof, list<congr_arg_kind> const & ks):
        m_type(type), m_proof(proof), m_arg_kinds(ks) {}
    expr const & get_type() const { return m_type; }
    expr const & get_proof() const { return m_proof; }
    list<congr_arg_kind> const & get_arg_kinds() const { return m_arg_kinds; }
    bool all_eq_kind() const;
};

class congr_lemma_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    congr_lemma_manager(app_builder & b, fun_info_manager & fm);
    ~congr_lemma_manager();
    typedef congr_lemma result;

    type_context & ctx();

    optional<result> mk_congr_simp(expr const & fn);
    optional<result> mk_congr_simp(expr const & fn, unsigned nargs);

    optional<result> mk_congr(expr const & fn);
    optional<result> mk_congr(expr const & fn, unsigned nargs);

    /** \brief If R is an equivalence relation, construct the congruence lemma

          R a1 a2 -> R b1 b2 -> (R a1 b1) <-> (R a2 b2) */
    optional<result> mk_rel_iff_congr(expr const & R);

    /** \brief Similar to previous one.
        It returns none if propext is not available.

          R a1 a2 -> R b1 b2 -> (R a1 b1) = (R a2 b2) */
    optional<result> mk_rel_eq_congr(expr const & R);
};
}
