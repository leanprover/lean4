/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class type_context_old;

enum class congr_arg_kind {
    /* It is a parameter for the congruence lemma, the parameter occurs in the left and right hand sides. */
    Fixed,
    /* It is not a parameter for the congruence lemma, the lemma was specialized for this parameter.
       This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. */
    FixedNoParam,
    /* The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i = b_i).
       a_i and b_i represent the left and right hand sides, and eq_i is a proof for their equality. */
    Eq,
    /* congr-simp lemma contains only one parameter for this kind of argument, and congr-lemmas contains two.
       They correspond to arguments that are subsingletons/propositions. */
    Cast,
    /* The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i == b_i).
       a_i and b_i represent the left and right hand sides, and eq_i is a proof for their heterogeneous equality. */
    HEq
};

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

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn, unsigned nargs);
/* Create a specialized theorem using (a prefix of) the arguments of the given application. */
optional<congr_lemma> mk_specialized_congr_simp(type_context_old & ctx, expr const & a);

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn, unsigned nargs);
/* Create a specialized theorem using (a prefix of) the arguments of the given application. */
optional<congr_lemma> mk_specialized_congr(type_context_old & ctx, expr const & a);

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn, unsigned nargs);

void initialize_congr_lemma();
void finalize_congr_lemma();
}
