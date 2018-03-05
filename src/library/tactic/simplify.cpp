/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#include <functional>
#include <iostream>
#include <limits>
#include "util/flet.h"
#include "util/freset.h"
#include "util/pair.h"
#include "util/optional.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/pp_options.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/expr_lt.h"
#include "library/locals.h"
#include "library/num.h"
#include "library/idx_metavar.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/attribute_manager.h"
#include "library/defeq_canonizer.h"
#include "library/relation_manager.h"
#include "library/app_builder.h"
#include "library/congr_lemma.h"
#include "library/fun_info.h"
#include "library/constructions/constructor.h"
#include "library/constructions/injective.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/simplify.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/simp_util.h"

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 1000000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL
#define LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_REWRITE
#define LEAN_DEFAULT_SIMPLIFY_REWRITE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_LIFT_EQ
#define LEAN_DEFAULT_SIMPLIFY_LIFT_EQ true
#endif

namespace lean {

simp_config::simp_config():
    m_max_steps(LEAN_DEFAULT_SIMPLIFY_MAX_STEPS),
    m_contextual(LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL),
    m_lift_eq(LEAN_DEFAULT_SIMPLIFY_LIFT_EQ),
    m_canonize_instances(true),
    m_canonize_proofs(false),
    m_use_axioms(false),
    m_zeta(false),
    m_beta(false),
    m_eta(true),
    m_proj(true),
    m_iota(true),
    m_iota_eqn(false),
    m_constructor_eq(true),
    m_single_pass(false),
    m_fail_if_unchanged(true),
    m_memoize(true) {
}

simp_config::simp_config(vm_obj const & obj) {
    m_max_steps          = force_to_unsigned(cfield(obj, 0));
    m_contextual         = to_bool(cfield(obj, 1));
    m_lift_eq            = to_bool(cfield(obj, 2));
    m_canonize_instances = to_bool(cfield(obj, 3));
    m_canonize_proofs    = to_bool(cfield(obj, 4));
    m_use_axioms         = to_bool(cfield(obj, 5));
    m_zeta               = to_bool(cfield(obj, 6));
    m_beta               = to_bool(cfield(obj, 7));
    m_eta                = to_bool(cfield(obj, 8));
    m_proj               = to_bool(cfield(obj, 9));
    m_iota               = to_bool(cfield(obj, 10));
    m_iota_eqn           = to_bool(cfield(obj, 11));
    m_constructor_eq     = to_bool(cfield(obj, 12));
    m_single_pass        = to_bool(cfield(obj, 13));
    m_fail_if_unchanged  = to_bool(cfield(obj, 14));
    m_memoize            = to_bool(cfield(obj, 15));
}

/* -----------------------------------
   Core simplification procedure.
   ------------------------------------ */

simp_result simplify_core_fn::join(simp_result const & r1, simp_result const & r2) {
    return ::lean::join(m_ctx, m_rel, r1, r2);
}

void simplify_core_fn::inc_num_steps() {
    m_num_steps++;
    if (m_num_steps > m_cfg.m_max_steps)
        throw exception("simplify failed, maximum number of steps exceeded");
}

bool simplify_core_fn::is_dependent_fn(expr const & f) {
    expr f_type = m_ctx.relaxed_whnf(m_ctx.infer(f));
    lean_assert(is_pi(f_type));
    return !is_arrow(f_type);
}

class simp_prover {
    simplify_core_fn & m_simp;
public:
    simp_prover(simplify_core_fn & s):m_simp(s) {}

    optional<expr> operator()(tmp_type_context &, expr const & e) {
        return m_simp.prove(e);
    }
};

bool simplify_core_fn::instantiate_emetas(tmp_type_context & tmp_ctx, list <expr> const & emetas,
                                          list<bool> const & instances) {
    simp_prover prover(*this);
    return instantiate_emetas_fn<simp_prover>(prover)(tmp_ctx, emetas, instances);
}

simp_result simplify_core_fn::lift_from_eq(simp_result const & r_eq) {
    if (!r_eq.has_proof()) return r_eq;
    expr new_pr = ::lean::lift_from_eq(m_ctx, m_rel, r_eq.get_proof());
    return simp_result(r_eq.get_new(), new_pr);
}

simp_lemmas simplify_core_fn::add_to_slss(simp_lemmas const & _slss, buffer<expr> const & ls) {
    simp_lemmas slss = _slss;
    for (unsigned i = 0; i < ls.size(); i++) {
        expr const & l = ls[i];
        try {
            slss = add(m_ctx, slss, mlocal_name(l), m_ctx.infer(l), l, LEAN_DEFAULT_PRIORITY);
            lean_simp_trace(m_ctx, name({"simplify", "context"}),
                            tout() << mlocal_name(l) << " : " << m_ctx.infer(l) << "\n";);
        } catch (exception & e) {}
    }
    return slss;
}

/* Given the application 'e', remove unnecessary casts of the form (eq.nrec a rfl) and (eq.drec a rfl) */
expr simplify_core_fn::remove_unnecessary_casts(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    ss_param_infos ss_infos = get_specialized_subsingleton_info(m_ctx, e);
    int i = -1;
    bool modified = false;
    for (ss_param_info const & ss_info : ss_infos) {
        i++;
        if (ss_info.is_subsingleton()) {
            while (is_constant(get_app_fn(args[i]))) {
                buffer<expr> cast_args;
                expr f_cast = get_app_args(args[i], cast_args);
                name n_f = const_name(f_cast);
                if (n_f == get_eq_rec_name() || n_f == get_eq_drec_name()) {
                    lean_assert(cast_args.size() == 6);
                    expr major_premise = cast_args[5];
                    expr f_major_premise = get_app_fn(major_premise);
                    if (is_constant(f_major_premise) && const_name(f_major_premise) == get_eq_refl_name()) {
                        args[i] = cast_args[3];
                        modified = true;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
    }
    return modified ? mk_app(f, args) : e;
}

expr simplify_core_fn::defeq_canonize_args_step(expr const & e) {
    buffer<expr> args;
    bool modified = false;
    expr f        = get_app_args(e, args);
    fun_info info = get_fun_info(m_ctx, f, args.size());
    unsigned i    = 0;
    for (param_info const & pinfo : info.get_params_info()) {
        lean_assert(i < args.size());
        expr new_a;
        if ((m_cfg.m_canonize_instances && pinfo.is_inst_implicit()) ||
            (m_cfg.m_canonize_proofs && pinfo.is_prop())) {
            new_a = m_defeq_canonizer.canonize(args[i], m_need_restart);
            lean_simp_trace(m_ctx, name({"simplify", "canonize"}),
                            tout() << "\n" << args[i] << "\n==>\n" << new_a << "\n";);
            if (new_a != args[i]) {
                modified = true;
                args[i] = new_a;
            }
        }
        i++;
    }

    return modified ? mk_app(f, args) : e;
}

/* Try user defined congruence lemmas */
simp_result simplify_core_fn::try_user_congrs(expr const & e) {
    simp_lemmas_for const * sls = m_slss.find(m_rel);
    if (!sls) return simp_result(e);

    if (auto cls = sls->find_congr(e)) {
        for (simp_lemma const & cl : *cls) {
            simp_result r = try_user_congr(e, cl);
            if (r.get_new() != e)
                return r;
        }
    }

    if (auto cls = sls->find_congr(head_index(expr_kind::Meta))) {
        for (simp_lemma const & cl : *cls) {
            simp_result r = try_user_congr(e, cl);
            if (r.get_new() != e)
                return r;
        }
    }

    return simp_result(e);
}

simp_result simplify_core_fn::try_user_congr(expr const & e, simp_lemma const & cl) {
    tmp_type_context tmp_ctx(m_ctx, cl.get_num_umeta(), cl.get_num_emeta());
    if (!tmp_ctx.is_def_eq(cl.get_lhs(), e))
        return simp_result(e);

    lean_simp_trace(tmp_ctx, name({"debug", "simplify", "try_congruence"}),
                    tout() << "(" << cl.get_id() << ") " << e << "\n";);

    bool simplified = false;

    buffer<expr> congr_hyps;
    to_buffer(cl.get_congr_hyps(), congr_hyps);

    buffer<type_context_old::tmp_locals> factories;
    buffer<name> relations;
    for (expr const & m : congr_hyps) {
        factories.emplace_back(m_ctx);
        type_context_old::tmp_locals & local_factory = factories.back();
        expr m_type = tmp_ctx.instantiate_mvars(tmp_ctx.infer(m));

        while (is_pi(m_type)) {
            expr d = instantiate_rev(binding_domain(m_type), local_factory.as_buffer().size(),
                                     local_factory.as_buffer().data());
            expr l = local_factory.push_local(binding_name(m_type), d, binding_info(m_type));
            lean_assert(!has_idx_metavar(l));
            m_type = binding_body(m_type);
        }
        m_type = instantiate_rev(m_type, local_factory.as_buffer().size(), local_factory.as_buffer().data());

        expr h_rel, h_lhs, h_rhs;
        lean_verify(is_simp_relation(tmp_ctx.env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel));
        {
            relations.push_back(const_name(h_rel));
            flet<simp_lemmas> set_slss(m_slss, m_cfg.m_contextual ? add_to_slss(m_slss, local_factory.as_buffer()) : m_slss);

            h_lhs = tmp_ctx.instantiate_mvars(h_lhs);
            lean_assert(!has_idx_metavar(h_lhs));

            simp_result r_congr_hyp;
            if (m_cfg.m_contextual || m_rel != const_name(h_rel)) {
                flet<name> set_name(m_rel, const_name(h_rel));
                freset<simplify_cache> reset_cache(m_cache);
                r_congr_hyp = visit(h_lhs, some_expr(e));
            } else {
                r_congr_hyp = visit(h_lhs, some_expr(e));
            }

            if (r_congr_hyp.has_proof())
                simplified = true;

            lean_assert(is_meta(h_rhs));
            buffer<expr> new_val_meta_args;
            expr new_val_meta = get_app_args(h_rhs, new_val_meta_args);
            lean_assert(is_metavar(new_val_meta));
            expr new_val = tmp_ctx.mk_lambda(new_val_meta_args, r_congr_hyp.get_new());
            tmp_ctx.assign(new_val_meta, new_val);

            expr pf_body = finalize(m_ctx, const_name(h_rel), r_congr_hyp).get_proof();
            expr pf      = local_factory.mk_lambda(pf_body);
            if (!tmp_ctx.is_def_eq(m, pf)) {
                lean_simp_trace(tmp_ctx, name({"simplify", "congruence"}),
                    tout() << "failed to unify proof " << pf << " of " << tmp_ctx.infer(pf););
                return simp_result(e);
            }
        }
    }

    if (!simplified)
        return simp_result(e);

    if (!instantiate_emetas(tmp_ctx, cl.get_emetas(), cl.get_instances()))
        return simp_result(e);

    for (unsigned i = 0; i < cl.get_num_umeta(); i++) {
        if (!tmp_ctx.is_uassigned(i))
            return simp_result(e);
    }

    expr e_s = tmp_ctx.instantiate_mvars(cl.get_rhs());
    expr pf = tmp_ctx.instantiate_mvars(cl.get_proof());

    simp_result r(e_s, pf);

    lean_simp_trace(tmp_ctx, name({"simplify", "congruence"}),
                    tout() << "(" << cl.get_id() << ") "
                    << "[" << e << " ==> " << e_s << "]\n";);

    return r;
}

/* Try to use congruence lemmas generated by the congr_lemma module.
   \remark these lemmas are for the equality relation. */
optional<simp_result> simplify_core_fn::try_auto_eq_congr(expr const & e) {
    lean_assert(m_rel == get_eq_name());
    lean_assert(is_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr_simp(m_ctx, e);
    if (!congr_lemma || length(congr_lemma->get_arg_kinds()) < args.size())
        return optional<simp_result>();

    buffer<simp_result> r_args;
    buffer<expr>        new_args;
    bool has_proof = false;
    bool has_cast = false;
    bool has_simplified = false;

    unsigned i = 0;

    // First pass, try to simplify all the Eq arguments
    for (congr_arg_kind const & ckind : congr_lemma->get_arg_kinds()) {
        switch (ckind) {
        case congr_arg_kind::HEq:
            lean_unreachable();
        case congr_arg_kind::Fixed:
        case congr_arg_kind::FixedNoParam:
            new_args.emplace_back(args[i]);
            break;
        case congr_arg_kind::Eq:
            {
                r_args.emplace_back(visit(args[i], some_expr(e)));
                simp_result & r_arg = r_args.back();
                new_args.emplace_back(r_arg.get_new());
                if (r_arg.has_proof())
                    has_proof = true;
                if (r_arg.get_new() != args[i])
                    has_simplified = true;
            }
            break;
        case congr_arg_kind::Cast:
            has_cast = true;
            new_args.emplace_back(args[i]);
            break;
        }
        i++;
    }

    if (!has_simplified) {
        simp_result r = simp_result(e);
        return optional<simp_result>(r);
    }

    if (!has_proof) {
        simp_result r = simp_result(mk_app(f, new_args));
        return optional<simp_result>(r);
    }

    // We have a proof, so we need to build the congruence lemma
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    buffer<expr> subst;

    i = 0;
    unsigned i_eq = 0;
    for (congr_arg_kind const & ckind : congr_lemma->get_arg_kinds()) {
        switch (ckind) {
        case congr_arg_kind::HEq:
            lean_unreachable();
        case congr_arg_kind::Fixed:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            break;
        case congr_arg_kind::FixedNoParam:
            break;
        case congr_arg_kind::Eq:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            {
                simp_result r_arg = finalize(m_ctx, m_rel, r_args[i_eq]);
                proof = mk_app(proof, r_arg.get_new(), r_arg.get_proof());
                subst.push_back(r_arg.get_new());
                subst.push_back(r_arg.get_proof());
            }
            type = binding_body(binding_body(type));
            i_eq++;
            break;
        case congr_arg_kind::Cast:
            lean_assert(has_cast);
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            break;
        }
        i++;
    }
    lean_assert(is_eq(type));
    expr rhs   = instantiate_rev(app_arg(type), subst.size(), subst.data());
    simp_result r(rhs, proof);

    if (has_cast) {
        r.update(remove_unnecessary_casts(r.get_new()));
    }

    return optional<simp_result>(r);
}

simp_result simplify_core_fn::congr_fun_arg(simp_result const & r_f, simp_result const & r_arg) {
    if (!r_f.has_proof() && !r_arg.has_proof()) return simp_result(mk_app(r_f.get_new(), r_arg.get_new()));
    else if (!r_f.has_proof()) return congr_arg(r_f.get_new(), r_arg);
    else if (!r_arg.has_proof()) return congr_fun(r_f, r_arg.get_new());
    else return congr(r_f, r_arg);
}

simp_result simplify_core_fn::congr(simp_result const & r_f, simp_result const & r_arg) {
    lean_assert(r_f.has_proof() && r_arg.has_proof());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e  = mk_app(r_f.get_new(), r_arg.get_new());
    expr pf = mk_congr(m_ctx, r_f.get_proof(), r_arg.get_proof());
    return simp_result(e, pf);
}

simp_result simplify_core_fn::congr_fun(simp_result const & r_f, expr const & arg) {
    lean_assert(r_f.has_proof());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e  = mk_app(r_f.get_new(), arg);
    expr pf = mk_congr_fun(m_ctx, r_f.get_proof(), arg);
    return simp_result(e, pf);
}

simp_result simplify_core_fn::congr_arg(expr const & f, simp_result const & r_arg) {
    lean_assert(r_arg.has_proof());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e  = mk_app(f, r_arg.get_new());
    expr pf = mk_congr_arg(m_ctx, f, r_arg.get_proof());
    return simp_result(e, pf);
}

simp_result simplify_core_fn::congr_funs(simp_result const & r_f, buffer<expr> const & args) {
    expr e = r_f.get_new();
    for (unsigned i = 0; i < args.size(); ++i) {
        e  = mk_app(e, args[i]);
    }
    if (!r_f.has_proof())
        return simp_result(e);
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        pf = mk_congr_fun(m_ctx, pf, args[i]);
    }
    return simp_result(e, pf);
}

simp_result simplify_core_fn::rewrite(expr const & e) {
    simp_lemmas_for const * sr = m_slss.find(m_rel);
    if (!sr) return simp_result(e);

    list<simp_lemma> const * srs = sr->find(e);
    if (!srs) {
        return simp_result(e);
    }

    for (simp_lemma const & lemma : *srs) {
        simp_result r = rewrite(e, lemma);
        if (!is_eqp(r.get_new(), e)) {
            lean_simp_trace_d(m_ctx, name({"simplify", "rewrite"}),
                              tout() << "[" << lemma.get_id() << "]: "
                              << e << " ==> " << r.get_new() << "\n";);
            return r;
        }
    }

    return simp_result(e);
}

bool simplify_core_fn::match(tmp_type_context & ctx, simp_lemma const & sl, expr const & t) {
    return ctx.match(sl.get_lhs(), t);
}

/* If both e and sl.get_lhs() are of the form (f ...),
   then we only trace the failure if the number of arguments is the same.

   This is simple filter to minimize the number of rewriting failures. */
static bool should_trace_failure(expr const & e, simp_lemma const & sl) {
    expr const & p = sl.get_lhs();
    expr const & fn = get_app_fn(p);
    if (!is_constant(fn)) return true;
    expr const & e_fn = get_app_fn(e);
    if (!is_constant(e_fn) || const_name(fn) != const_name(e_fn)) return true;
    return get_app_num_args(e) == get_app_num_args(p);
}

simp_result simplify_core_fn::rewrite_core(expr const & e, simp_lemma const & sl) {
    tmp_type_context tmp_ctx(m_ctx, sl.get_num_umeta(), sl.get_num_emeta());

    if (!match(tmp_ctx, sl, e)) {
        if (lean_is_trace_enabled(name({"simplify", "rewrite_failure"})) &&
            should_trace_failure(e, sl)) {
            lean_simp_trace_d(m_ctx, name({"simplify", "rewrite_failure"}),
                              tout() << "fail to match '" << sl.get_id() << "':\n"
                              << e << "\n=?=\n" << sl.get_lhs() << "\n--------------\n";);
        }
        return simp_result(e);
    }

    if (!instantiate_emetas(tmp_ctx, sl.get_emetas(), sl.get_instances())) {
        lean_simp_trace_d(m_ctx, name({"simplify", "failure"}),
                          lean_trace_init_bool(name({"simplify", "failure"}), get_pp_implicit_name(), true);
                          tout() << "fail to instantiate emetas: '" << sl.get_id() << "' at\n"
                          << e << "\npartially instantiated lemma:\n" << tmp_ctx.instantiate_mvars(sl.get_proof()) << "\n";);
        return simp_result(e);
    }

    for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
        if (!tmp_ctx.is_uassigned(i)) {
            lean_simp_trace_d(m_ctx, name({"simplify", "failure"}),
                              lean_trace_init_bool(name({"simplify", "failure"}), get_pp_universes_name(), true);
                              tout() << "fail to instantiate umetas: '" << sl.get_id() << "'\n";);
            return simp_result(e);
        }
    }

    expr new_lhs = tmp_ctx.instantiate_mvars(sl.get_lhs());
    expr new_rhs = tmp_ctx.instantiate_mvars(sl.get_rhs());

    if (new_rhs == e) {
        /* TODO(Leo): remove after we have arithmetic normalizer.
           The unifier at type context has support for offset equalities.
           So, it can match
                  ?x + 0 =?= t + 1
           by assigning
                  ?x := t + 1 */
        return simp_result(e);
    }

    if (sl.is_permutation()) {
        if (!is_lt(new_rhs, new_lhs, false, &m_ctx.lctx())) {
            lean_simp_trace(tmp_ctx, name({"simplify", "perm"}),
                            tout() << "perm rejected: " << new_rhs << " !< " << new_lhs << "\n";);
            return simp_result(e);
        }
    }

    expr pf = tmp_ctx.instantiate_mvars(sl.get_proof());
    return simp_result(new_rhs, pf);
}

simp_result simplify_core_fn::rewrite(expr const & e, simp_lemma const & sl) {
    if (!is_app(e))
        return rewrite_core(e, sl);
    unsigned e_nargs   = get_app_num_args(e);
    unsigned lhs_nargs = get_app_num_args(sl.get_lhs());
    if (e_nargs == lhs_nargs)
        return rewrite_core(e, sl);
    if (e_nargs < lhs_nargs)
        return simp_result(e);
    buffer<expr> extra_args;
    unsigned i = e_nargs;
    auto it = e;
    while (i > lhs_nargs) {
        --i;
        extra_args.push_back(app_arg(it));
        it = app_fn(it);
    }
    lean_assert(get_app_num_args(it) == lhs_nargs);
    simp_result it_r = rewrite_core(it, sl);
    if (it_r.get_new() == it)
        return simp_result(e);
    expr new_e = mk_rev_app(it_r.get_new(), extra_args);
    new_e      = reduce(new_e);
    if (!it_r.has_proof())
        return simp_result(new_e);
    expr pr = it_r.get_proof();
    i = extra_args.size();
    while (i > 0) {
        --i;
        pr = mk_congr_fun(m_ctx, pr, extra_args[i]);
    }
    return simp_result(new_e, pr);
}

simp_result simplify_core_fn::propext_rewrite(expr const & e) {
    if (m_rel != get_eq_name()) return simp_result(e);
    flet<name> set_rel(m_rel, get_iff_name());
    freset<simplify_cache> reset_cache(m_cache);
    simp_result r = rewrite(e);
    if (!r.has_proof()) return r;
    expr new_pr = mk_app(m_ctx, get_propext_name(), r.get_proof());
    return simp_result(r.get_new(), new_pr);
}

simp_result simplify_core_fn::visit(expr const & e, optional<expr> const & parent) {
    check_system("simplify");
    inc_num_steps();
    lean_trace_inc_depth("simplify");
    lean_simp_trace(m_ctx, "simplify", tout() << m_rel << ": " << e << "\n";);

    if (m_cfg.m_memoize) {
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
    }

    simp_result curr_result(e);
    if (auto r1 = pre(e, parent)) {
        if (!r1->second) {
            if (m_cfg.m_memoize)
                m_cache.insert(mk_pair(e, r1->first));
            return r1->first;
        }
        curr_result = r1->first;
    }

    while (true) {
        simp_result new_result;
        switch (curr_result.get_new().kind()) {
        case expr_kind::Local:
        case expr_kind::Sort:
        case expr_kind::Constant:
            new_result = curr_result;
            break;
        case expr_kind::Meta:
            new_result = curr_result;
            new_result.update(m_ctx.instantiate_mvars(new_result.get_new()));
            break;
        case expr_kind::Macro:
            new_result = join(curr_result, visit_macro(curr_result.get_new()));
            break;
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Lambda:
            new_result = join(curr_result, visit_lambda(curr_result.get_new()));
            break;
        case expr_kind::Pi:
            new_result = join(curr_result, visit_pi(curr_result.get_new()));
            break;
        case expr_kind::App:
            new_result = join(curr_result, visit_app(curr_result.get_new()));
            break;
        case expr_kind::Let:
            new_result = join(curr_result, visit_let(curr_result.get_new()));
            break;
        }

        if (m_cfg.m_constructor_eq && simplify_constructor_eq_constructor(new_result)) {
            curr_result = new_result;
            /* continue simplifying */
        } else if (auto r2 = post(new_result.get_new(), parent)) {
            if (!r2->second) {
                curr_result = join(new_result, r2->first);
                break;
            } else if (r2->first.get_new() == curr_result.get_new()) {
                break;
            } else {
                curr_result = join(new_result, r2->first);
                if (m_cfg.m_single_pass)
                    break;
                /* continue simplifying */
            }
        } else {
            curr_result = new_result;
            break;
        }
    }

    if (m_cfg.m_lift_eq && m_rel != get_eq_name()) {
        simp_result eq_result;
        {
            flet<name> use_eq(m_rel, get_eq_name());
            freset<simplify_cache> reset_cache(m_cache);
            eq_result = visit(curr_result.get_new(), parent);
        }
        if (eq_result.get_new() != curr_result.get_new()) {
            curr_result = join(curr_result, lift_from_eq(eq_result));
            curr_result = join(curr_result, visit(curr_result.get_new(), parent));
        }
    }

    if (m_cfg.m_memoize)
        m_cache.insert(mk_pair(e, curr_result));
    return curr_result;
}

simp_result simplify_core_fn::visit_fn(expr const & e) {
    lean_assert(m_rel == get_eq_name());
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    simp_result r_f = visit(f, some_expr(e));
    return congr_funs(r_f, args);
}

expr simplify_core_fn::reduce(expr e) {
    return reduce_beta_eta_proj_iota(m_ctx, e, m_cfg.m_beta, m_cfg.m_eta, m_cfg.m_proj, m_cfg.m_iota);
}

simp_result simplify_core_fn::reduce(simp_result r) {
    r.update(reduce(r.get_new()));
    return r;
}

simp_result simplify_core_fn::visit_app(expr const & _e) {
    lean_assert(is_app(_e));
    expr e = reduce(_e);
    e      = should_defeq_canonize() ? defeq_canonize_args_step(e) : e;
    if (!is_app(e))
        return visit(e, none_expr());
    // (1) Try user-defined congruences
    simp_result r_user = try_user_congrs(e);
    if (r_user.has_proof()) {
        if (m_rel == get_eq_name()) {
            return reduce(join(r_user, visit_fn(r_user.get_new())));
        } else {
            return reduce(r_user);
        }
    }

    if (m_rel == get_eq_name()) {
        // (2) Synthesize congruence lemma
        optional<simp_result> r_args = try_auto_eq_congr(e);
        if (r_args) {
            return reduce(join(*r_args, visit_fn(r_args->get_new())));
        }


        // (3) Fall back on generic binary congruence
        expr const & f = app_fn(e);
        expr const & arg = app_arg(e);

        simp_result r_f = visit(f, some_expr(e));

        if (is_dependent_fn(f)) {
            if (r_f.has_proof()) return reduce(congr_fun(r_f, arg));
            else return reduce(mk_app(r_f.get_new(), arg));
        } else {
            simp_result r_arg = visit(arg, some_expr(e));
            return reduce(congr_fun_arg(r_f, r_arg));
        }
    }

    return simp_result(e);
}

bool simplify_core_fn::simplify_constructor_eq_constructor(simp_result & r) {
    if (m_rel != get_eq_name())
        return false; /* TODO(Leo): we can add support for <-> */
    expr A, lhs, rhs;
    if (!is_eq(r.get_new(), A, lhs, rhs))
        return false;
    optional<name> c1 = is_gintro_rule_app(m_ctx.env(), lhs);
    if (!c1) return false;
    optional<name> c2 = is_gintro_rule_app(m_ctx.env(), rhs);
    if (!c2) return false;

    if (*c1 != *c2) {
        if (optional<expr> not_eq_prf = mk_constructor_ne_constructor_proof(m_ctx, lhs, rhs)) {
            expr eq_false_prf = mk_app(m_ctx, get_eq_false_intro_name(), *not_eq_prf);
            simp_result new_r(mk_false(), eq_false_prf);
            r = join_eq(m_ctx, r, new_r);
            return true;
        } else {
            return false;
        }
    } else {
        A = whnf_ginductive(m_ctx, A);
        expr const & A_fn   = get_app_fn(A);
        if (!is_constant(A_fn) || !is_ginductive(m_ctx.env(), const_name(A_fn)))
            return false;
        unsigned A_nparams = get_ginductive_num_params(m_ctx.env(), const_name(A_fn));
        if (get_app_num_args(lhs) <= A_nparams)
            return false;
        name inj_eq_name = mk_injective_eq_name(*c1);
        optional<declaration> inj_eq_decl = m_ctx.env().find(inj_eq_name);
        if (!inj_eq_decl)
            return false;
        /* We use the `*.inj` lemma for computing the arguments for `*.inj_eq` lemma. */
        try {
            name inj_name = mk_injective_name(*c1);
            optional<declaration> inj_decl = m_ctx.env().find(inj_name);
            if (!inj_decl)
                return false;
            unsigned inj_arity = get_arity(inj_decl->get_type());
            type_context_old::tmp_locals locals(m_ctx);
            expr H   = locals.push_local("_h", r.get_new());
            expr inj = mk_app(m_ctx, inj_name, inj_arity, H);
            buffer<expr> inj_args;
            expr const & inj_fn = get_app_args(inj, inj_args);
            expr inj_eq_pr = mk_app(mk_constant(inj_eq_name, const_levels(inj_fn)), inj_args.size() - 1, inj_args.data());
            expr inj_eq    = m_ctx.infer(inj_eq_pr);
            expr new_lhs, new_rhs;
            lean_verify(is_eq(inj_eq, new_lhs, new_rhs));
            simp_result new_r(new_rhs, inj_eq_pr);
            r = join_eq(m_ctx, r, new_r);
            return true;
        } catch (exception &) {
            return false;
        }
    }
}

optional<expr> simplify_core_fn::prove(expr const &) {
    return none_expr();
}

simp_result simplify_core_fn::visit_lambda(expr const & e) {
    return simp_result(reduce(e));
}

simp_result simplify_core_fn::visit_pi(expr const & e) {
    return try_user_congrs(e);
}

simp_result simplify_core_fn::visit_let(expr const & e) {
    if (m_cfg.m_zeta)
        return visit(instantiate(let_body(e), let_value(e)), none_expr());
    else
        return simp_result(e);
}

simp_result simplify_core_fn::visit_macro(expr const & e) {
    return simp_result(e);
}

optional<pair<simp_result, bool>> simplify_core_fn::pre(expr const &, optional<expr> const &) {
    return optional<pair<simp_result, bool>>();
}

optional<pair<simp_result, bool>> simplify_core_fn::post(expr const &, optional<expr> const &) {
    return optional<pair<simp_result, bool>>();
}

simplify_core_fn::simplify_core_fn(type_context_old & ctx, defeq_canonizer::state & dcs, simp_lemmas const & slss,
                                   simp_config const & cfg):
    m_ctx(ctx), m_defeq_canonizer(m_ctx, dcs), m_slss(slss), m_cfg(cfg) {
}

simp_result simplify_core_fn::simplify(expr const & e) {
    m_cache.clear();
    simp_result r(e);
    while (true) {
        m_need_restart = false;
        r = join(r, visit(r.get_new(), none_expr()));
        if (!m_need_restart || !should_defeq_canonize())
            return r;
        m_cache.clear();
    }
}

simp_result simplify_core_fn::operator()(name const & rel, expr const & e) {
    if (m_rel != rel) {
        flet<name> _(m_rel, rel);
        freset<simplify_cache> reset_cache(m_cache);
        return simplify(e);
    } else {
        return simplify(e);
    }
}

static expr mk_mpr(type_context_old & ctx, name const & rel, expr const & h1, expr const & h2) {
    lean_assert(rel == get_eq_name() || rel == get_iff_name());
    if (rel == get_eq_name())
        return mk_eq_mpr(ctx, h1, h2);
    else
        return mk_iff_mpr(ctx, h1, h2);
}

optional<expr> simplify_core_fn::prove_by_simp(name const & rel, expr const & e) {
    lean_assert(rel == get_eq_name() || rel == get_iff_name());
    simp_result r = operator()(rel, e);
    name rrel;
    expr lhs, rhs;
    if (is_relation(m_ctx.env(), r.get_new(), rrel, lhs, rhs) &&
        is_refl_relation(m_ctx.env(), rrel) &&
        m_ctx.is_def_eq(lhs, rhs)) {
        if (r.has_proof()) {
            return some_expr(mk_mpr(m_ctx, rel, r.get_proof(), mk_refl(m_ctx, rrel, lhs)));
        } else {
            return some_expr(mk_refl(m_ctx, rrel, lhs));
        }
    } else if (is_true(r.get_new())) {
        if (r.has_proof()) {
            return some_expr(mk_mpr(m_ctx, rel, r.get_proof(), mk_true_intro()));
        } else {
            return some_expr(mk_true_intro());
        }
    }
    lean_simp_trace(m_ctx, name({"simplify", "failure"}), tout() << "proof stuck at: " << r.get_new() << "\n";);
    return none_expr();
}

/* -----------------------------------
   simplify_ext_core_fn
   ------------------------------------ */

simplify_ext_core_fn::simplify_ext_core_fn(type_context_old & ctx, defeq_can_state & dcs, simp_lemmas const & slss,
                                           simp_config const & cfg):
    simplify_core_fn(ctx, dcs, slss, cfg) {
}

simp_result simplify_ext_core_fn::visit_lambda(expr const & e) {
    if (m_rel != get_eq_name() || !m_cfg.m_use_axioms) return simp_result(e);
    type_context_old::tmp_locals locals(m_ctx);
    expr it = e;
    while (is_lambda(it)) {
        expr d = instantiate_rev(binding_domain(it), locals.size(), locals.as_buffer().data());
        expr l = locals.push_local(binding_name(it), d, binding_info(it));
        it = binding_body(it);
    }
    it = instantiate_rev(it, locals.size(), locals.as_buffer().data());

    simp_result r = visit(it, some_expr(e));
    expr new_body = r.get_new();

    if (new_body == it)
        return simp_result(reduce(e));

    if (!r.has_proof())
        return reduce(simp_result(locals.mk_lambda(new_body)));

    /* TODO(Leo): the following code can be optimized using the same trick used at
       forall_congr. */
    buffer<expr> const & ls = locals.as_buffer();
    unsigned i = ls.size();
    expr pr    = r.get_proof();
    while (i > 0) {
        --i;
        expr const & l = ls[i];
        expr lam_pr    = m_ctx.mk_lambda(l, pr);
        pr             = mk_funext(m_ctx, lam_pr);
    }
    return reduce(simp_result(locals.mk_lambda(new_body), pr));
}

simp_result simplify_ext_core_fn::forall_congr(expr const & e) {
    lean_assert(m_rel == get_eq_name() || m_rel == get_iff_name());
    buffer<expr> pis;
    type_context_old::tmp_locals locals(m_ctx);
    expr it = e;
    while (is_pi(it)) {
        expr d = instantiate_rev(binding_domain(it), locals.as_buffer().size(), locals.as_buffer().data());
        if (m_ctx.is_prop(d))
            break;
        pis.push_back(it);
        locals.push_local(binding_name(it), d, binding_info(it));
        it = binding_body(it);
    }
    buffer<expr> const & ls = locals.as_buffer();
    lean_assert(pis.size() == ls.size());
    expr body          = instantiate_rev(it, ls.size(), ls.data());
    simp_result body_r = visit(body, some_expr(e));
    expr new_body      = body_r.get_new();
    expr abst_new_body = abstract_locals(new_body, ls.size(), ls.data());
    name lemma_name    = m_rel == get_eq_name() ? get_forall_congr_eq_name() : get_forall_congr_name();
    if (body_r.has_proof()) {
        expr pr      = body_r.get_proof();
        expr Pr      = abstract_locals(pr, ls.size(), ls.data());
        unsigned i   = pis.size();
        expr Q       = abst_new_body;
        expr R       = abst_new_body;
        while (i > 0) {
            --i;
            expr pi      = pis[i];
            expr A       = binding_domain(pi);
            level A_lvl  = get_level(m_ctx, m_ctx.infer(ls[i]));
            expr P       = mk_lambda(binding_name(pi), A, binding_body(pi));
            expr Q       = mk_lambda(binding_name(pi), A, R);
            expr H       = mk_lambda(binding_name(pi), A, Pr);
            Pr           = mk_app(mk_constant(lemma_name, {A_lvl}), A, P, Q, H);
            R            = update_binding(pi, A, R);
        }
        lean_assert(closed(Pr));
        return simp_result(R, Pr);
    } else if (new_body == body) {
        return simp_result(e);
    } else {
        expr R = abst_new_body;
        unsigned i = pis.size();
        while (i > 0) {
            --i;
            R = update_binding(pis[i], binding_domain(pis[i]), R);
        }
        return simp_result(R);
    }
    return simp_result(e);
}

simp_result simplify_ext_core_fn::imp_congr(expr const & e) {
    expr const & a  = binding_domain(e);
    expr const & b  = binding_body(e);
    simp_result r_a = visit(a, some_expr(e));
    if (m_cfg.m_contextual) {
        type_context_old::tmp_locals locals(m_ctx);
        expr h = locals.push_local("_h", r_a.get_new());
        flet<simp_lemmas> set_slss(m_slss, add_to_slss(m_slss, locals.as_buffer()));
        freset<simplify_cache> reset_cache(m_cache);
        simp_result r_b = visit(b, some_expr(e));
        if (r_a.get_new() == a && r_b.get_new() == b) {
            return e;
        } else if (!r_a.has_proof() && !r_b.has_proof()) {
            return simp_result(update_binding(e, r_a.get_new(), r_b.get_new()));
        } else {
            expr fn   = mk_constant(m_rel == get_eq_name() ? get_imp_congr_ctx_eq_name() : get_imp_congr_ctx_name());
            expr pr_a = finalize(m_ctx, m_rel, r_a).get_proof();
            expr pr_b = locals.mk_lambda(finalize(m_ctx, m_rel, r_b).get_proof());
            expr pr = mk_app({fn, a, b, r_a.get_new(), r_b.get_new(), pr_a, pr_b});
            return simp_result(update_binding(e, r_a.get_new(), r_b.get_new()), pr);
        }
    } else {
        simp_result r_b = visit(b, some_expr(e));
        if (r_a.get_new() == a && r_b.get_new() == b) {
            return e;
        } else if (!r_a.has_proof() && !r_b.has_proof()) {
            return simp_result(update_binding(e, r_a.get_new(), r_b.get_new()));
        } else {
            expr fn   = mk_constant(m_rel == get_eq_name() ? get_imp_congr_eq_name() : get_imp_congr_name());
            expr pr_a = finalize(m_ctx, m_rel, r_a).get_proof();
            expr pr_b = finalize(m_ctx, m_rel, r_b).get_proof();
            expr pr = mk_app({fn, a, b, r_a.get_new(), r_b.get_new(), pr_a, pr_b});
            return simp_result(update_binding(e, r_a.get_new(), r_b.get_new()), pr);
        }
    }
}

simp_result simplify_ext_core_fn::visit_pi(expr const & e) {
    if ((m_rel == get_eq_name() && m_cfg.m_use_axioms) || m_rel == get_iff_name()) {
        if (m_ctx.is_prop(e)) {
            if (!m_ctx.is_prop(binding_domain(e)))
                return forall_congr(e);
            else if (is_arrow(e))
                return imp_congr(e);
        }
    }
    return simplify_core_fn::visit_pi(e);
}

simp_result simplify_ext_core_fn::visit_macro(expr const & e) {
    if (is_annotation(e)) {
        return visit(get_annotation_arg(e), none_expr());
    } else {
        return simplify_core_fn::visit_macro(e);
    }
}

simp_result simplify_ext_core_fn::visit_let(expr const & e) {
    /* TODO(Leo): when m_zeta is false, we need to implement efficient code for checking whether the abstraction of
       a let-body is type correct or not */
    return simplify_core_fn::visit_let(e);
}

static optional<pair<simp_result, bool>> to_ext_result(simp_result const & r) {
    return optional<pair<simp_result, bool>>(r, true);
}

static optional<pair<simp_result, bool>> no_ext_result() {
    return optional<pair<simp_result, bool>>();
}

optional<pair<simp_result, bool>> simplify_fn::pre(expr const &, optional<expr> const &) {
    return no_ext_result();
}

// TODO(Leo): move to a different file
static optional<expr> unfold_using_nontrivial_eqns(type_context_old & ctx, expr const & e) {
    if (!is_app(e)) return none_expr();
    expr const & f = get_app_fn(e);
    if (!is_constant(f)) return none_expr();
    if (has_simple_eqn_lemma(ctx.env(), const_name(f))) return none_expr();
    type_context_old::transparency_scope scope(ctx, transparency_mode::Semireducible);
    return ctx.unfold_definition(e);
}

optional<pair<simp_result, bool>> simplify_fn::post(expr const & e, optional<expr> const &) {
    if (auto r = unfold_step(m_ctx, e, m_to_unfold, false))
        return to_ext_result(simp_result(*r));
    if (m_cfg.m_iota_eqn) {
        if (auto r = unfold_using_nontrivial_eqns(m_ctx, e))
            return to_ext_result(simp_result(*r));
    }
    simp_result r = rewrite(e);
    if (r.get_new() != e) {
        return to_ext_result(r);
    } else if (!m_cfg.m_use_axioms) {
        return no_ext_result();
    } else {
        r = propext_rewrite(e);
        if (r.get_new() != e)
            return to_ext_result(r);
        else
            return no_ext_result();
    }
}

optional<expr> simplify_fn::prove(expr const & e) {
    return prove_by_simp(get_iff_name(), e);
}

class vm_simplify_fn : public simplify_ext_core_fn {
    vm_obj       m_a;
    vm_obj       m_prove;
    vm_obj       m_pre;
    vm_obj       m_post;
    tactic_state m_s;

    optional<pair<simp_result, bool>> invoke_fn(vm_obj const & fn, expr const & e, optional<expr> const & parent) {
        m_s = set_mctx_lctx_dcs(m_s, m_ctx.mctx(), m_ctx.lctx(), m_defeq_canonizer.get_state());
        vm_obj r = invoke(fn, m_a, to_obj(m_slss), to_obj(m_rel), to_obj(parent), to_obj(e), to_obj(m_s));
        /* r : tactic_state (A × expr × option expr × bool) */
        if (optional<tactic_state> new_s = tactic::is_success(r)) {
            m_s = *new_s;
            m_ctx.set_mctx(m_s.mctx());
            m_defeq_canonizer.set_state(m_s.dcs());
            vm_obj t = tactic::get_success_value(r);
            /* t : A × expr × option expr × bool */
            m_a        = cfield(t, 0);
            vm_obj t1  = cfield(t, 1);
            expr new_e = to_expr(cfield(t1, 0));
            vm_obj t2  = cfield(t1, 1);
            optional<expr> new_pr;
            vm_obj vpr = cfield(t2, 0);
            if (!is_none(vpr))
                new_pr = to_expr(get_some_value(vpr));
            bool flag  = to_bool(cfield(t2, 1));
            return optional<pair<simp_result, bool>>(simp_result(new_e, new_pr), flag);
        } else {
            return no_ext_result();
        }
    }

    virtual optional<pair<simp_result, bool>> pre(expr const & e, optional<expr> const & parent) override {
        return invoke_fn(m_pre, e, parent);
    }

    virtual optional<pair<simp_result, bool>> post(expr const & e, optional<expr> const & parent) override {
        return invoke_fn(m_post, e, parent);
    }

    virtual optional<expr> prove(expr const & e) override {
        auto s = mk_tactic_state_for(m_ctx.env(), m_ctx.get_options(), m_s.decl_name(), m_ctx.lctx(), e);
        vm_obj r_obj           = invoke(m_prove, m_a, to_obj(s));
        optional<tactic_state> s_new = tactic::is_success(r_obj);
        if (!s_new || s_new->goals()) return none_expr();
        metavar_context mctx   = s_new->mctx();
        expr result            = mctx.instantiate_mvars(s_new->main());
        if (has_expr_metavar(result)) return none_expr();
        m_a = cfield(r_obj, 0);
        m_ctx.set_mctx(mctx);
        return some_expr(result);
    }

public:
    vm_simplify_fn(type_context_old & ctx, defeq_can_state & dcs, simp_lemmas const & slss, simp_config const & cfg,
                   vm_obj const & prove, vm_obj const & pre, vm_obj const & post, tactic_state const & s):
        simplify_ext_core_fn(ctx, dcs, slss, cfg),
        m_prove(prove), m_pre(pre), m_post(post),
        m_s(s) {}

    pair<vm_obj, simp_result> operator()(vm_obj const & a, name const & rel, expr const & e) {
        m_a = a;
        auto r = simplify_ext_core_fn::operator()(rel, e);
        return mk_pair(m_a, r);
    }
};

class tactic_simplify_fn : public simplify_fn {
    tactic_state m_s;
    vm_obj       m_prove;

    optional<expr> prove_core(expr const & e) {
        auto s = mk_tactic_state_for(m_ctx.env(), m_ctx.get_options(), m_s.decl_name(), m_ctx.lctx(), e);
        vm_obj r_obj = invoke(m_prove, to_obj(s));
        optional<tactic_state> s_new = tactic::is_success(r_obj);
        if (!s_new || s_new->goals()) return none_expr();
        metavar_context mctx   = s_new->mctx();
        expr result            = mctx.instantiate_mvars(s_new->main());
        if (has_expr_metavar(result)) return none_expr();
        m_ctx.set_mctx(mctx);
        return some_expr(result);
    }

    virtual optional<expr> prove(expr const & e) override {
        if (auto r = prove_core(e))
            return r;
        else
            return simplify_fn::prove(e);
    }

public:
    tactic_simplify_fn(type_context_old & ctx, defeq_canonizer::state & dcs, simp_lemmas const & slss, list<name> const & to_unfold,
                       simp_config const & cfg, tactic_state const & s, vm_obj const & prove):
        simplify_fn(ctx, dcs, slss, to_unfold, cfg),
        m_s(s),
        m_prove(prove) {
    }
};

/*
meta constant simplify
  (s : simp_lemmas)
  (u : list name)
  (e : expr)
  (c : simp_config)
  (r : name)
  (prove : tactic unit)
  : tactic (expr × expr)
*/
vm_obj tactic_simplify(vm_obj const & slss, vm_obj const & u, vm_obj const & e, vm_obj const & c, vm_obj const & rel,
                       vm_obj const & prove, vm_obj const & _s) {
    tactic_state s = tactic::to_state(_s);
    try {
        simp_config cfg(c);
        tactic_state_context_cache cache(s);
        type_context_old ctx     = cache.mk_type_context(transparency_mode::Reducible);
        defeq_can_state dcs  = s.dcs();
        tactic_simplify_fn simp(ctx, dcs, to_simp_lemmas(slss), to_list_name(u), cfg, s, prove);
        simp_result result   = simp(to_name(rel), to_expr(e));
        if (!cfg.m_fail_if_unchanged || result.get_new() != to_expr(e)) {
            result = finalize(ctx, to_name(rel), result);
            tactic_state new_s = set_dcs(s, dcs);
            return tactic::mk_success(mk_vm_pair(to_obj(result.get_new()), to_obj(result.get_proof())), new_s);
        } else {
            return tactic::mk_exception("simplify tactic failed to simplify", s);
        }
    } catch (exception & e) {
        return tactic::mk_exception(e, s);
    }
}

static vm_obj ext_simplify_core(vm_obj const & a, vm_obj const & c, simp_lemmas const & slss, vm_obj const & prove,
                                vm_obj const & pre, vm_obj const & post, name const & r, expr const & e,
                                tactic_state s) {
    try {
        simp_config cfg(c);
        tactic_state_context_cache cache(s);
        type_context_old ctx     = cache.mk_type_context(transparency_mode::Reducible);
        defeq_can_state dcs  = s.dcs();
        vm_simplify_fn simp(ctx, dcs, slss, cfg, prove, pre, post, s);
        pair<vm_obj, simp_result> p = simp(a, r, e);
        if (!cfg.m_fail_if_unchanged || p.second.get_new() != e) {
            vm_obj const & a   = p.first;
            simp_result result = finalize(ctx, r, p.second);
            tactic_state new_s = set_dcs(s, dcs);
            return tactic::mk_success(mk_vm_pair(a, mk_vm_pair(to_obj(result.get_new()), to_obj(result.get_proof()))), new_s);
        } else {
            return tactic::mk_exception("simplify tactic failed to simplify", s);
        }
    } catch (exception & e) {
        return tactic::mk_exception(e, s);
    }
}

/*
meta constant ext_simplify_core
  {A : Type}
  (a : A)
  (c : simp_config)
  (l : simp_lemmas)
  (prove : A → tactic A)
  (pre : A → name → simp_lemmas → option expr → expr → tactic (A × expr × option expr × bool))
  (post : A → name → simp_lemmas → option expr → expr → tactic (A × expr × option expr × bool))
  (r : name) :
  expr → tactic (A × expr × expr)
*/
vm_obj tactic_ext_simplify_core(unsigned DEBUG_CODE(num), vm_obj const * args) {
    lean_assert(num == 10);
    return ext_simplify_core(args[1], args[2], to_simp_lemmas(args[3]), args[4], args[5], args[6],
                             to_name(args[7]), to_expr(args[8]), tactic::to_state(args[9]));
}

void initialize_simplify() {
    register_trace_class("simplify");
    register_trace_class(name({"simplify", "failure"}));
    register_trace_class(name({"simplify", "rewrite_failure"}));
    register_trace_class(name({"simplify", "context"}));
    register_trace_class(name({"simplify", "canonize"}));
    register_trace_class(name({"simplify", "congruence"}));
    register_trace_class(name({"simplify", "rewrite"}));
    register_trace_class(name({"simplify", "perm"}));
    register_trace_class(name({"debug", "simplify", "try_congruence"}));

    DECLARE_VM_BUILTIN(name({"tactic", "simplify"}), tactic_simplify);
    declare_vm_builtin(name({"tactic", "ext_simplify_core"}),
                       "tactic_ext_simplify_core", 10, tactic_ext_simplify_core);
}

void finalize_simplify() {
}
}
