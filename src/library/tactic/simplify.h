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
    bool instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta,
                            list<expr> const & emetas, list<bool> const & instances);
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

    /* Rewriting
       Remark: the rewriting methods are implemented on this base class once and for all,
       but used in subclasses.*/
    simp_result rewrite(expr const & e);
    simp_result rewrite(expr const & e, simp_lemma const & sl);
    simp_result propext_rewrite(expr const & e);

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

    optional<expr> prove_by_simp(name const & rel, expr const & e);
};

/* Extend simplify_core_fn functionality by assuming function
   extensionality and propositional extensionality. */
class simplify_ext_core_fn : public simplify_core_fn {
protected:
    bool m_use_axioms;
    simp_result forall_congr(expr const & e);
    simp_result imp_congr(expr const & e);
    virtual simp_result visit_lambda(expr const & e) override;
    virtual simp_result visit_pi(expr const & e) override;
    virtual simp_result visit_let(expr const & e) override;
public:
    simplify_ext_core_fn(type_context & ctx, simp_lemmas const & slss,
                         unsigned max_steps, bool contextual, bool lift_eq,
                         bool canonize_instances, bool canonize_proofs, bool use_axioms);
};

/* Default (bottom-up) simplifier: reduce projections, and apply simplification lemmas */
class simplify_fn : public simplify_ext_core_fn {
protected:
    virtual optional<pair<simp_result, bool>> pre(expr const & e, optional<expr> const & parent) override;
    virtual optional<pair<simp_result, bool>> post(expr const & e, optional<expr> const & parent) override;
public:
    simplify_fn(type_context & ctx, simp_lemmas const & slss,
                unsigned max_steps, bool contextual, bool lift_eq,
                bool canonize_instances, bool canonize_proofs, bool use_axioms):
        simplify_ext_core_fn(ctx, slss, max_steps, contextual, lift_eq,
                             canonize_instances, canonize_proofs, use_axioms) {}
};

void initialize_simplify();
void finalize_simplify();
}
