/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/vm/vm.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {
/* n is the internal name of a hypothesis that represents an equality */
vm_obj tactic_subst_core(name const & n, bool symm, tactic_state const & s) {
    try {
        metavar_decl g             = *s.get_main_goal_decl();
        local_context lctx         = g.get_context();
        local_decl d               = *lctx.get_local_decl(n);
        expr lhs, rhs;
        is_eq(d.get_type(), lhs, rhs);
        buffer<expr> to_revert;
        if (symm)
            std::swap(lhs, rhs);
        to_revert.push_back(lhs);
        to_revert.push_back(d.mk_ref());
        tactic_state s1 = revert(to_revert, s);
        lean_assert(to_revert.size() >= 2);
        buffer<name> lhsH;
        optional<tactic_state> s2 = intron(2, s1, lhsH);
        if (!s2) return mk_tactic_exception("subst tactic failed, unexpected failure during intro", s);
        lctx                 = s2->get_main_goal_decl()->get_context();
        expr type            = s2->get_main_goal_decl()->get_type();
        lhs                  = lctx.get_local_decl(lhsH[0])->mk_ref();
        expr H               = lctx.get_local_decl(lhsH[1])->mk_ref();
        bool depH            = depends_on(type, H);
        expr new_type        = instantiate(abstract_local(type, lhs), rhs);
        metavar_context mctx = s2->mctx();
        type_context ctx     = mk_type_context_for(*s2, mctx);
        app_builder builder  = mk_app_builder_for(ctx);
        expr motive;
        if (depH) {
            new_type = instantiate(abstract_local(new_type, H), builder.mk_eq_refl(rhs));
            if (symm) {
                motive = ctx.mk_lambda({lhs, H}, type);
            } else {
                motive = mk_lambda("H", builder.mk_eq(rhs, lhs), type);
                motive = ctx.mk_lambda(lhs, motive);
            }
        } else {
            motive   = ctx.mk_lambda(lhs, type);
        }
        expr major   = symm ? H : builder.mk_eq_symm(H);
        expr new_M   = mctx.mk_metavar_decl(lctx, new_type);
        expr minor   = new_M;
        expr new_val = depH ? builder.mk_eq_drec(motive, minor, major) : builder.mk_eq_rec(motive, minor, major);
        mctx.assign(head(s2->goals()), new_val);
        list<expr> new_gs(new_M, tail(s.goals()));
        tactic_state s3 = set_mctx_goals(*s2, mctx, new_gs);
        vm_obj o4    = clear_internal(lhsH[1], s3);
        optional<tactic_state> s4 = is_tactic_success(o4);
        if (!s4) return o4;
        vm_obj o5    = clear_internal(lhsH[0], *s4);
        optional<tactic_state> s5 = is_tactic_success(o5);
        if (!s5) return o5;
        optional<tactic_state> s6 = intron(to_revert.size() - 2, *s5);
        if (!s6) return mk_tactic_exception("subst tactic failed, unexpected failure during intro", s);
        return mk_tactic_success(*s6);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_subst(name const & n, tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx         = g->get_context();
    optional<local_decl> d     = lctx.get_local_decl_from_user_name(n);
    if (!d)
        return mk_tactic_exception(sstream() << "subst tactic failed, unknown '" << n << "' hypothesis", s);
    expr const & type = d->get_type();
    expr lhs, rhs;
    if (is_eq(type, lhs, rhs)) {
        if (is_local(rhs) && !depends_on(rhs, lhs)) {
            return tactic_subst_core(d->get_name(), true, s);
        } else if (is_local(lhs) && !depends_on(lhs, rhs)) {
            return tactic_subst_core(d->get_name(), false, s);
        } else {
            return mk_tactic_exception(sstream() << "subst tactic failed, hypothesis '"
                                       << n << "' is not of the form (x = t) or (t = x)", s);
        }
    } else {
        bool found = false;
        vm_obj r;
        lctx.for_each_after(*d, [&](local_decl const & d2) {
                if (found) return;
                expr lhs, rhs;
                if (is_eq(d2.get_type(), lhs, rhs)) {
                    if (is_local(lhs) && mlocal_name(lhs) == d->get_name() && !depends_on(rhs, lhs)) {
                        found = true;
                        r     = tactic_subst_core(d2.get_name(), false, s);
                    } else if (is_local(rhs) && mlocal_name(rhs) == d->get_name() && !depends_on(lhs, rhs)) {
                        found = true;
                        r     = tactic_subst_core(d2.get_name(), true, s);
                    }
                }
            });
        if (found) {
            return r;
        } else {
            return mk_tactic_exception(sstream() << "subst tactic failed, hypothesis '"
                                       << n << "' is not a variable nor an equation of the form (x = t) or (t = x)", s);
        }
    }
}

vm_obj tactic_subst(vm_obj const & n, vm_obj const & s) {
    return tactic_subst(to_name(n), to_tactic_state(s));
}

void initialize_subst_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "subst"}), tactic_subst);
}

void finalize_subst_tactic() {
}
}
