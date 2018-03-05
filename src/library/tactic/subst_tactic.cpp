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
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/app_builder_tactics.h"

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
    lean_assert(is_local(H));
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
    expr new_type       = instantiate(abstract_local(type, lhs), rhs);
    type_context_old ctx2   = mk_type_context_for(env, opts, mctx, g2.get_context(), m);
    expr motive;
    if (depH2) {
        new_type = instantiate(abstract_local(new_type, H2), mk_eq_refl(ctx2, rhs));
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
            expr new_type = instantiate(abstract_local(type, H2), H2_prime_symm);
            motive = ctx2.mk_lambda({lhs, H2_prime}, new_type);
        }
    } else {
        lean_subst_trace(tout() << "non dep-elim\n";);
        motive   = ctx2.mk_lambda(lhs, type);
    }
    expr major   = symm ? H2 : mk_eq_symm(ctx2, H2);
    expr mvar3   = ctx2.mk_metavar_decl(lctx, new_type);
    expr minor   = mvar3;
    expr new_val = depH2 ? mk_eq_drec(ctx2, motive, minor, major) : mk_eq_rec(ctx2, motive, minor, major);
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
            lean_assert(check_hypothesis_in_context(mctx, mvar, mlocal_name(to_revert[i+2])));
            lean_assert(check_hypothesis_in_context(mctx, *mvar6, new_Hnames[i]));
            new_subst.insert(mlocal_name(to_revert[i+2]), lctx.get_local(new_Hnames[i]));
        }
        new_subst.insert(mlocal_name(init_lhs), apply(rhs, new_subst));
        *subst = new_subst;
    }
    lean_subst_trace_state(*mvar6, "after intro remaining reverted hypotheses:\n");
    return *mvar6;
}

/* n is the internal name of a hypothesis that represents an equality */
vm_obj tactic_subst_core(name const & n, bool symm, tactic_state const & s) {
    try {
        metavar_context mctx = s.mctx();
        expr mvar = head(s.goals());
        expr H    = mctx.get_local(mvar, n);
        expr new_mvar = subst(s.env(), s.get_options(), transparency_mode::Semireducible, mctx, mvar, H, symm, nullptr);
        return tactic::mk_success(set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals()))));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_subst(expr const & l, tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx       = s.mctx();
    local_context lctx         = g->get_context();
    if (!is_local(l))
        return tactic::mk_exception(sstream() << "subst tactic failed, given expression is not a local constant", s);
    optional<local_decl> d     = lctx.find_local_decl(l);
    if (!d)
        return tactic::mk_exception(sstream() << "subst tactic failed, unknown '" << mlocal_pp_name(l) << "' hypothesis", s);
    expr type = mctx.instantiate_mvars(d->get_type());
    expr lhs, rhs;
    if (is_eq(type, lhs, rhs)) {
        if (is_local(rhs) && !depends_on(lhs, mctx, lctx, rhs)) {
            return tactic_subst_core(d->get_name(), true, s);
        } else if (is_local(lhs) && !depends_on(rhs, mctx, lctx, lhs)) {
            return tactic_subst_core(d->get_name(), false, s);
        } else {
            return tactic::mk_exception(sstream() << "subst tactic failed, hypothesis '"
                                        << mlocal_pp_name(l) << "' is not of the form (x = t) or (t = x)", s);
        }
    } else {
        bool found = false;
        vm_obj r;
        lctx.for_each_after(*d, [&](local_decl const & d2) {
                if (found) return;
                expr lhs, rhs;
                expr type = mctx.instantiate_mvars(d2.get_type());
                if (is_eq(type, lhs, rhs)) {
                    if (is_local(lhs) && mlocal_name(lhs) == d->get_name() && !depends_on(rhs, mctx, lctx, lhs)) {
                        found = true;
                        r     = tactic_subst_core(d2.get_name(), false, s);
                    } else if (is_local(rhs) && mlocal_name(rhs) == d->get_name() && !depends_on(lhs, mctx, lctx, rhs)) {
                        found = true;
                        r     = tactic_subst_core(d2.get_name(), true, s);
                    }
                }
            });
        if (found) {
            return r;
        } else {
            return tactic::mk_exception(sstream() << "subst tactic failed, hypothesis '"
                                       << mlocal_pp_name(l) << "' is not a variable nor an equation of the form (x = t) or (t = x)", s);
        }
    }
}

vm_obj tactic_subst(vm_obj const & e, vm_obj const & s) {
    return tactic_subst(to_expr(e), tactic::to_state(s));
}

void initialize_subst_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "subst_core"}), tactic_subst);
    register_trace_class(name{"tactic", "subst"});
}

void finalize_subst_tactic() {
}
}
