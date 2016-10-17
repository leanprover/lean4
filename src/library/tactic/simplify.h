/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/simp_result.h"

namespace lean {
/* Core simplification procedure. It performs the following tasks:
   1- Manages the cache;
   2- Applies congruence lemmas;
   3- Canonizes instances & proofs;
   4- Manages contextual rewriting

   This is a base class for many simplification strategies.
   Its behavior can be configured by overriding its virtual methods.
   This class does *not* apply any simp lemma, nor it tries to
   put subterms in weak-head-normal-form.

   This class also does *not* use axioms. For example, it will
   not use funext to go inside lambda terms. This feature is provided
   by subclasses.

   Remark: it is debatable whether the options m_lift_eq, m_canonize_instances and
   m_canonize_proofs really need to be here. They may be moved to subclasses in the
   future.
*/
class simplify_core_fn {
protected:
    typedef expr_struct_map<simp_result> simplify_cache;

    type_context              m_ctx;
    name                      m_rel;
    simp_lemmas               m_slss;
    simplify_cache            m_cache;

    /* Logging */
    unsigned                  m_num_steps{0};
    bool                      m_need_restart{false};

    /* Options */
    unsigned                  m_max_steps;
    bool                      m_contextual;
    bool                      m_lift_eq;
    bool                      m_canonize_instances;
    bool                      m_canonize_proofs;

    simp_result join(simp_result const & r1, simp_result const & r2);
    void inc_num_steps();
    bool is_dependent_fn(expr const & f);
    bool should_defeq_canonize() const { return m_canonize_instances || m_canonize_proofs; }
    bool instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances);
    simp_result lift_from_eq(simp_result const & r_eq);
    simp_lemmas add_to_slss(simp_lemmas const & slss, buffer<expr> const & ls);
    expr remove_unnecessary_casts(expr const & e);
    expr defeq_canonize_args_step(expr const & e);

    /* Congruence */
    simp_result try_user_congrs(expr const & e);
    simp_result try_user_congr(expr const & e, simp_lemma const & cr);

    optional<simp_result> try_auto_eq_congr(expr const & e);

    simp_result congr_fun_arg(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr_fun(simp_result const & r_f, expr const & arg);
    simp_result congr_arg(expr const & f, simp_result const & r_arg);
    simp_result congr_funs(simp_result const & r_f, buffer<expr> const & args);

    /* Visitors */
    virtual optional<pair<simp_result, bool>> pre(expr const & e, optional<expr> const & parent);
    virtual optional<pair<simp_result, bool>> post(expr const & e, optional<expr> const & parent);

    virtual optional<expr> prove(expr const & goal);

    simp_result visit_fn(expr const & e);
    virtual simp_result visit_lambda(expr const & e);
    virtual simp_result visit_pi(expr const & e);
    virtual simp_result visit_let(expr const & e);
    virtual simp_result visit_app(expr const & e);
    virtual simp_result visit_macro(expr const & e);

    virtual simp_result visit(expr const & e, optional<expr> const & parent);

public:
    simplify_core_fn(type_context & ctx, simp_lemmas const & slss,
                     unsigned max_steps, bool contextual, bool lift_eq,
                     bool canonize_instances, bool canonize_proofs);

    environment const & env() const;
    simp_result operator()(name const & rel, expr const & e);
};

simp_result simplify(type_context & tctx, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e);
simp_result simplify(type_context & tctx, name const & rel, simp_lemmas const & simp_lemmas, expr const & e);

simp_result simplify(type_context & tctx, type_context & tctx_whnf, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e);
simp_result simplify(type_context & tctx, type_context & tctx_whnf, name const & rel, simp_lemmas const & simp_lemmas, expr const & e);

optional<expr> prove_eq_by_simp(type_context & tctx, type_context & tctx_whnf, simp_lemmas const & simp_lemmas, expr const & e);

name get_simplify_prefix_name();
name get_simplify_max_steps_name();
name get_simplify_contextual_name();
name get_simplify_rewrite_name();
name get_simplify_lift_eq_name();
name get_simplify_canonize_instances_fixed_point_name();
name get_simplify_canonize_proofs_fixed_point_name();
name get_simplify_canonize_subsingletons_name();

void initialize_simplify();
void finalize_simplify();
}
