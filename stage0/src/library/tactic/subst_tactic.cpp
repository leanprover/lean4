/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/subst_tactic.h"

namespace lean {
/* For debugging purposes, make sure H is in the local context for mvar */
bool check_hypothesis_in_context(metavar_context const & mctx, expr const & mvar, name const & H) {
    local_context lctx = mctx.get_metavar_decl(mvar).get_context();
    if (!lctx.find_local_decl(H)) {
        lean_unreachable();
        return false;
    }
    return true;
}

expr subst(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
           expr const & mvar, expr const & H, bool symm, hsubstitution * subst) {
    #define lean_subst_trace(CODE) lean_trace(name({"tactic", "subst"}), CODE)
#define lean_subst_trace_state(MVAR, MSG) lean_trace(name({"tactic", "subst"}), tactic_state S = mk_tactic_state_for_metavar(env, opts, "subst", mctx, MVAR); type_context_old TMP_CTX = mk_cacheless_type_context_for(S, m); scope_trace_env _scope1(env, TMP_CTX); tout() << MSG << S.pp_core() << "\n";)

    lean_subst_trace_state(mvar, "initial:\n");
    lean_assert(mctx.find_metavar_decl(mvar));
    lean_assert(is_fvar(H));
    metavar_decl g      = mctx.get_metavar_decl(mvar);
    type_context_old ctx    = mk_type_context_for(env, opts, mctx, g.get_context(), m);
    expr H_type         = ctx.instantiate_mvars(ctx.infer(H));
    expr lhs, rhs;
    lean_verify(is_eq(H_type, lhs, rhs));
    if (symm) std::swap(lhs, rhs);
    expr init_lhs = lhs;
    buffer<expr> to_revert;
    to_revert.push_back(lhs);
    to_revert.push_back(H);
    bool preserve_to_revert_order = true;
    expr mvar1 = revert(env, opts, mctx, mvar, to_revert, preserve_to_revert_order);
    lean_subst_trace(tout() << "to_revert:"; for (auto h : to_revert) tout() << " " << h; tout() << "\n";);
    lean_subst_trace_state(mvar1, "after revert:\n");
    lean_assert(to_revert.size() >= 2);
    buffer<name> lhsH2;
    bool use_unused_names = false;
    optional<expr> mvar2 = intron(env, opts, mctx, mvar1, 2, lhsH2, use_unused_names);
    if (!mvar2) throw exception("subst tactic failed, unexpected failure during intro");
    lean_subst_trace_state(*mvar2, "after intro2:\n");
    metavar_decl g2     = mctx.get_metavar_decl(*mvar2);
    local_context lctx  = g2.get_context();
    expr type           = g2.get_type();
    lhs                 = lctx.get_local(lhsH2[0]);
    expr H2             = lctx.get_local(lhsH2[1]);
    bool depH2          = depends_on(type, H2);
    expr new_type       = instantiate(abstract(type, lhs), rhs);
    type_context_old ctx2   = mk_type_context_for(env, opts, mctx, g2.get_context(), m);
    expr motive;
    if (depH2) {
        new_type = instantiate(abstract(new_type, H2), mk_eq_refl(ctx2, rhs));
        if (symm) {
            lean_subst_trace(tout() << "dep-elim and symm\n";);
            motive = ctx2.mk_lambda({lhs, H2}, type);
        } else {
            lean_subst_trace(tout() << "dep-elim\n";);
            /* `type` depends on (H2 : lhs = rhs). So, we use the following trick to avoid a type incorrect motive.
               1- Create a new local (H2_prime : rhs = lhs)
               2- Create new_type := type [H2_prime.symm / H2]
                  `new_type` is type correct because `H2` and `H2_prime.symm` are definitionally equal by proof irrelevance.
               3- Create motive by abstracting `lhs` and `H2_prime` in `new_type`.
             */
            type_context_old::tmp_locals locals(ctx2);
            expr H2_prime = locals.push_local("_h", mk_eq(ctx2, rhs, lhs));
            expr H2_prime_symm = mk_eq_symm(ctx2, H2_prime);
            /* replace H2 in type with H2'.symm, where H2' is a new local that is def-eq to H2.symm */
            expr new_type = instantiate(abstract(type, H2), H2_prime_symm);
            motive = ctx2.mk_lambda({lhs, H2_prime}, new_type);
        }
    } else {
        lean_subst_trace(tout() << "non dep-elim\n";);
        motive   = ctx2.mk_lambda(lhs, type);
    }
    expr major   = symm ? H2 : mk_eq_symm(ctx2, H2);
    expr mvar3   = ctx2.mk_metavar_decl(lctx, new_type);
    expr minor   = mvar3;
    expr new_val = depH2 ? mk_eq_rec(ctx2, motive, minor, major) : mk_eq_ndrec(ctx2, motive, minor, major);
    mctx = ctx2.mctx();
    mctx.assign(*mvar2, new_val);
    expr mvar4   = clear(mctx, mvar3, H2);
    expr mvar5   = clear(mctx, mvar4, lhs);
    buffer<name> new_Hnames;
    use_unused_names = false;
    optional<expr> mvar6 = intron(env, opts, mctx, mvar5, to_revert.size() - 2, new_Hnames, use_unused_names);
    if (!mvar6) throw exception("subst tactic failed, unexpected failure when re-introducing dependencies");
    lean_assert(new_Hnames.size() == to_revert.size() - 2);
    if (subst) {
        local_context lctx = mctx.get_metavar_decl(*mvar6).get_context();
        hsubstitution new_subst;
        for (unsigned i = 0; i < to_revert.size() - 2; i++) {
            lean_assert(check_hypothesis_in_context(mctx, mvar, fvar_name(to_revert[i+2])));
            lean_assert(check_hypothesis_in_context(mctx, *mvar6, new_Hnames[i]));
            new_subst.insert(fvar_name(to_revert[i+2]), lctx.get_local(new_Hnames[i]));
        }
        new_subst.insert(fvar_name(init_lhs), apply(rhs, new_subst));
        *subst = new_subst;
    }
    lean_subst_trace_state(*mvar6, "after intro remaining reverted hypotheses:\n");
    return *mvar6;
}

void initialize_subst_tactic() {
}

void finalize_subst_tactic() {
}
}
