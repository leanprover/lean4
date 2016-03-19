/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include "util/lbool.h"
#include "kernel/environment.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "kernel/expr_pair.h"
#include "library/justification.h"

namespace lean {
/** \brief Converter used in the kernel */
class default_converter : public converter {
protected:
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> expr_pair_set;
    environment             m_env;
    bool                    m_memoize;
    expr_struct_map<expr>   m_whnf_core_cache;
    expr_struct_map<expr>   m_whnf_cache;
    equiv_manager           m_eqv_manager;
    expr_pair_set           m_failure_cache;

    // The two auxiliary fields are set when the public methods whnf and is_def_eq are invoked.
    // The goal is to avoid to keep carrying them around.
    type_checker *                              m_tc;
    delayed_justification *                     m_jst;

    virtual bool is_stuck(expr const & e);
    virtual optional<expr> norm_ext(expr const & e);

    expr infer_type(expr const & e) { return converter::infer_type(*m_tc, e); }
    optional<expr> expand_macro(expr const & m);
    expr whnf_core(expr const & e);
    expr unfold_name_core(expr e, unsigned w);
    expr unfold_names(expr const & e, unsigned w);
    expr whnf_core(expr e, unsigned w);

    expr whnf(expr const & e_prime);

    bool is_def_eq_binding(expr t, expr s);
    bool is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(levels const & ls1, levels const & ls2);

    lbool quick_is_def_eq(expr const & t, expr const & s, bool use_hash = false);
    bool is_def_eq_args(expr t, expr s);
    bool try_eta_expansion_core(expr const & t, expr const & s);
    bool try_eta_expansion(expr const & t, expr const & s) {
        return try_eta_expansion_core(t, s) || try_eta_expansion_core(s, t);
    }
    bool is_def_eq(expr const & t, expr const & s);
    bool is_def_eq_app(expr const & t, expr const & s);
    bool is_def_eq_proof_irrel(expr const & t, expr const & s);

    bool failed_before(expr const & t, expr const & s) const;
    void cache_failure(expr const & t, expr const & s);

    bool is_prop(expr const & e);

    bool is_def_eq_core(expr const & t, expr const & s);

    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };
    reduction_status lazy_delta_reduction_step(expr & t_n, expr & s_n);
    lbool lazy_delta_reduction(expr & t_n, expr & s_n);
    reduction_status ext_reduction_step(expr & t_n, expr & s_n);
    virtual lbool reduce_def_eq(expr & t_n, expr & s_n);
    virtual bool postpone_is_def_eq(expr const & t, expr const & s);
public:
    default_converter(environment const & env, bool memoize = true);

    virtual optional<declaration> is_delta(expr const & e) const;
    virtual bool is_opaque(declaration const & d) const;

    virtual optional<expr> is_stuck(expr const & e, type_checker & c);
    virtual expr whnf(expr const & e_prime, type_checker & c);
    virtual bool is_def_eq(expr const & t, expr const & s, type_checker & c);
};

void initialize_default_converter();
void finalize_default_converter();
}
