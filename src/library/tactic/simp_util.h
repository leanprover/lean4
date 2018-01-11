/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#define lean_simp_trace(CTX, N, CODE) lean_trace(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)
#define lean_simp_trace_d(CTX, N, CODE) lean_trace_d(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)

namespace lean {
template<typename Prover>
class instantiate_emetas_fn {
    Prover & m_prover;
public:
    instantiate_emetas_fn(Prover & prover):
        m_prover(prover) {}

    bool operator()(tmp_type_context & tmp_ctx, unsigned num_emeta,
                    list<expr> const & emetas, list<bool> const & instances) {
        bool failed = false;
        unsigned i  = num_emeta;
        for_each2(emetas, instances, [&](expr const & mvar, bool const & is_instance) {
                i--;
                if (failed) return;
                expr mvar_type = tmp_ctx.instantiate_mvars(tmp_ctx.infer(mvar));
                if (has_idx_metavar(mvar_type)) {
                    failed = true;
                    return;
                }

                if (tmp_ctx.is_eassigned(i)) return;

                if (is_instance) {
                    if (auto v = tmp_ctx.ctx().mk_class_instance(mvar_type)) {
                        if (!tmp_ctx.is_def_eq(mvar, *v)) {
                            lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                            tout() << "unable to assign instance for: " << mvar_type << "\n";);
                            failed = true;
                            return;
                        }
                    } else {
                        lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                        tout() << "unable to synthesize instance for: " << mvar_type << "\n";);
                        failed = true;
                        return;
                    }
                }

                if (tmp_ctx.is_eassigned(i)) return;

                if (tmp_ctx.ctx().is_prop(mvar_type)) {
                    if (auto pf = m_prover(tmp_ctx, mvar_type)) {
                        lean_verify(tmp_ctx.is_def_eq(mvar, *pf));
                        return;
                    } else {
                        lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                        tout() << "failed to prove: " << mvar << " : " << mvar_type << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                    tout() << "failed to assign: " << mvar << " : " << mvar_type << "\n";);
                    failed = true;
                    return;
                }
            });
        return !failed;
    }
};
}
