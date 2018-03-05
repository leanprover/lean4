/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {
static vm_obj exact(expr const & e, transparency_mode const & m, tactic_state s) {
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        tactic_state_context_cache cache(s);
        type_context_old ctx     = cache.mk_type_context(m);
        expr mvar            = head(s.goals());
        if (is_metavar(e) && mlocal_name(mvar) == mlocal_name(e)) {
            return tactic::mk_exception("invalid exact tactic, trying to solve goal using itself", s);
        }
        if (!ctx.is_def_eq(mvar, e)) {
            expr e_type          = ctx.infer(e);
            if (!ctx.is_def_eq(g->get_type(), e_type)) {
                auto thunk = [=]() {
                    format r("exact tactic failed, type mismatch, given expression has type");
                    unsigned indent = get_pp_indent(s.get_options());
                    r += nest(indent, line() + pp_expr(s, e_type));
                    r += line() + format("but is expected to have type");
                    r += nest(indent, line() + pp_expr(s, g->get_type()));
                    return r;
                };
                return tactic::mk_exception(thunk, s);
            } else {
                /* Ocurrs check failed */
                auto thunk = [=]() {
                    format r("exact tactic failed, failed to assign ");
                    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
                    type_context_old ctx = mk_cacheless_type_context_for(s, transparency_mode::All);
                    formatter fmt    = fmtf(s.env(), s.get_options(), ctx);
                    unsigned indent  = get_pp_indent(s.get_options());
                    r += nest(indent, line() + fmt(e));
                    r += line() + format("to metavariable ") + fmt(mvar) + format(" (possible cause: occurs check failed)");
                    return r;
                };
                return tactic::mk_exception(thunk, s);
            }
        }
        auto mctx = ctx.mctx();
        return tactic::mk_success(set_mctx_goals(s, mctx, tail(s.goals())));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_exact(vm_obj const & e, vm_obj const & m, vm_obj const & s) {
    return exact(to_expr(e), to_transparency_mode(m), tactic::to_state(s));
}

void initialize_exact_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "exact"}), tactic_exact);
}

void finalize_exact_tactic() {
}
}
