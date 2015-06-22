/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include "util/lbool.h"
#include "kernel/justification.h"
#include "kernel/environment.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "kernel/expr_pair.h"

namespace lean {
/** \brief Converter used in the kernel */
class default_converter : public converter {
protected:
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> expr_pair_set;
    environment                                 m_env;
    bool                                        m_memoize;
    expr_struct_map<expr>                       m_whnf_core_cache;
    expr_struct_map<pair<expr, constraint_seq>> m_whnf_cache;
    equiv_manager                               m_eqv_manager;
    expr_pair_set                               m_failure_cache;

    // The two auxiliary fields are set when the public methods whnf and is_def_eq are invoked.
    // The goal is to avoid to keep carrying them around.
    type_checker *                              m_tc;
    delayed_justification *                     m_jst;

    virtual bool is_stuck(expr const & e);
    virtual optional<pair<expr, constraint_seq>> norm_ext(expr const & e);

    pair<expr, constraint_seq> infer_type(expr const & e) { return converter::infer_type(*m_tc, e); }
    constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j);
    optional<expr> expand_macro(expr const & m);
    optional<expr> d_norm_ext(expr const & e, constraint_seq & cs);
    expr whnf_core(expr const & e);
    expr unfold_name_core(expr e, unsigned w);
    expr unfold_names(expr const & e, unsigned w);
    expr whnf_core(expr e, unsigned w);

    expr whnf(expr const & e_prime, constraint_seq & cs);

    pair<bool, constraint_seq> to_bcs(bool b) { return mk_pair(b, constraint_seq()); }
    pair<bool, constraint_seq> to_bcs(bool b, constraint const & c) { return mk_pair(b, constraint_seq(c)); }
    pair<bool, constraint_seq> to_bcs(bool b, constraint_seq const & cs) { return mk_pair(b, cs); }

    bool is_def_eq_binding(expr t, expr s, constraint_seq & cs);
    bool is_def_eq(level const & l1, level const & l2, constraint_seq & cs);
    bool is_def_eq(levels const & ls1, levels const & ls2, constraint_seq & cs);

    static pair<lbool, constraint_seq> to_lbcs(lbool l) { return mk_pair(l, constraint_seq()); }
    static pair<lbool, constraint_seq> to_lbcs(lbool l, constraint const & c) { return mk_pair(l, constraint_seq(c)); }
    static pair<lbool, constraint_seq> to_lbcs(pair<bool, constraint_seq> const & bcs) {
        return mk_pair(to_lbool(bcs.first), bcs.second);
    }

    lbool quick_is_def_eq(expr const & t, expr const & s, constraint_seq & cs, bool use_hash = false);
    bool is_def_eq_args(expr t, expr s, constraint_seq & cs);
    bool is_app_of(expr t, name const & f_name);
    bool try_eta_expansion_core(expr const & t, expr const & s, constraint_seq & cs);
    bool try_eta_expansion(expr const & t, expr const & s, constraint_seq & cs) {
        return try_eta_expansion_core(t, s, cs) || try_eta_expansion_core(s, t, cs);
    }
    bool is_def_eq(expr const & t, expr const & s, constraint_seq & cs);
    bool is_def_eq_app(expr const & t, expr const & s, constraint_seq & cs);
    bool is_def_eq_proof_irrel(expr const & t, expr const & s, constraint_seq & cs);

    bool failed_before(expr const & t, expr const & s) const;
    void cache_failure(expr const & t, expr const & s);

    pair<bool, constraint_seq> is_prop(expr const & e);
    pair<expr, constraint_seq> whnf(expr const & e_prime);
    pair<bool, constraint_seq> is_def_eq_core(expr const & t, expr const & s);
    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s);

    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };
    reduction_status lazy_delta_reduction_step(expr & t_n, expr & s_n, constraint_seq & cs);
    lbool lazy_delta_reduction(expr & t_n, expr & s_n, constraint_seq & cs);
    reduction_status ext_reduction_step(expr & t_n, expr & s_n, constraint_seq & cs);
    virtual lbool reduce_def_eq(expr & t_n, expr & s_n, constraint_seq & cs);

    virtual bool postpone_is_def_eq(expr const & t, expr const & s);
public:
    default_converter(environment const & env, bool memoize = true);

    virtual optional<declaration> is_delta(expr const & e) const;
    virtual bool is_opaque(declaration const & d) const;

    virtual optional<expr> is_stuck(expr const & e, type_checker & c);
    virtual pair<expr, constraint_seq> whnf(expr const & e_prime, type_checker & c);
    virtual pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst);
};

void initialize_default_converter();
void finalize_default_converter();
}
