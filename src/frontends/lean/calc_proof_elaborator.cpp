/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/metavar_closure.h"
#include "frontends/lean/util.h"
#include "frontends/lean/local_context.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/calc.h"

namespace lean {
static optional<pair<expr, expr>> apply_symmetry(environment const & env, local_context & ctx, name_generator & ngen,
                                                 expr const & e, expr const & e_type, tag g) {
    buffer<expr> args;
    expr const & op = get_app_args(e_type, args);
    if (is_constant(op) && args.size() >= 2) {
        if (auto t = get_calc_symm_info(env, const_name(op))) {
            name symm; unsigned nargs; unsigned nunivs;
            std::tie(symm, nargs, nunivs) = *t;
            unsigned sz  = args.size();
            expr  lhs    = args[sz-2];
            expr  rhs    = args[sz-1];
            levels lvls;
            for (unsigned i = 0; i < nunivs; i++)
                lvls = levels(mk_meta_univ(ngen.next()), lvls);
            expr symm_op = mk_constant(symm, lvls);
            buffer<expr> inv_args;
            for (unsigned i = 0; i < nargs - 3; i++)
                inv_args.push_back(ctx.mk_meta(ngen, none_expr(), g));
            inv_args.push_back(lhs);
            inv_args.push_back(rhs);
            inv_args.push_back(e);
            expr new_e = mk_app(symm_op, inv_args);
            args[sz-2] = rhs;
            args[sz-1] = lhs;
            expr new_e_type = mk_app(op, args);
            return some(mk_pair(new_e, new_e_type));
        }
    }
    return optional<pair<expr, expr>>();
}

/** \brief Create a "choice" constraint that postpones the resolution of a calc proof step.

    By delaying it, we can perform quick fixes such as:
      - adding symmetry
      - adding !
      - adding subst
*/
constraint mk_calc_proof_cnstr(environment const & env, local_context const & _ctx,
                               expr const & m, expr const & _e,
                               constraint_seq const & cs, unifier_config const & cfg,
                               info_manager * im, bool relax) {
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator const & _ngen) {
        local_context ctx = _ctx;
        expr e            = _e;
        name_generator ngen(_ngen);
        type_checker_ptr tc(mk_type_checker(env, ngen.mk_child(), relax));
        constraint_seq new_cs = cs;
        expr e_type = tc->infer(e, new_cs);
        e_type      = tc->whnf(e_type, new_cs);
        tag g       = e.get_tag();
        // add '!' is needed
        while (is_pi(e_type)) {
            binder_info bi = binding_info(e_type);
            if (!bi.is_implicit() && !bi.is_inst_implicit()) {
                if (!has_free_var(binding_body(e_type), 0)) {
                    // if the rest of the type does not reference argument,
                    // then we also stop consuming arguments
                    break;
                }
            }
            expr imp_arg = ctx.mk_meta(ngen, some_expr(binding_domain(e_type)), g);
            e            = mk_app(e, imp_arg, g);
            e_type       = tc->whnf(instantiate(binding_body(e_type), imp_arg), new_cs);
        }

        auto try_alternative = [&](expr const & e, expr const & e_type) {
            justification new_j            = mk_type_mismatch_jst(e, e_type, meta_type);
            constraint_seq fcs             = new_cs;
            if (!tc->is_def_eq(e_type, meta_type, new_j, fcs))
                throw unifier_exception(new_j, s);
            buffer<constraint> cs_buffer;
            fcs.linearize(cs_buffer);
            metavar_closure cls(meta);
            cls.add(meta_type);
            cls.mk_constraints(s, j, relax, cs_buffer);
            cs_buffer.push_back(mk_eq_cnstr(meta, e, j, relax));

            unifier_config new_cfg(cfg);
            new_cfg.m_discard    = false;
            unify_result_seq seq = unify(env, cs_buffer.size(), cs_buffer.data(), ngen, substitution(), new_cfg);
            auto p = seq.pull();
            lean_assert(p);
            substitution new_s     = p->first.first;
            constraints  postponed = map(p->first.second,
                                         [&](constraint const & c) {
                                             // we erase internal justifications
                                             return update_justification(c, j);
                                         });
            if (im)
                im->instantiate(new_s);
            constraints r = cls.mk_constraints(new_s, j, relax);
            return append(r, postponed);
        };

        std::unique_ptr<exception> saved_ex;
        try {
            return try_alternative(e, e_type);
        } catch (exception & ex) {
            saved_ex.reset(ex.clone());
        }

        if (auto p = apply_symmetry(env, ctx, ngen, e, e_type, g)) {
            try { return try_alternative(p->first, p->second); } catch (exception &) {}
        }

        saved_ex->rethrow();
        lean_unreachable();
    };
    bool owner = false;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::Epilogue), owner, j, relax);
}
}
