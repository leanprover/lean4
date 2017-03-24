/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <frontends/lean/elaborator.h>
#include "kernel/for_each_fn.h"
#include "library/annotation.h"
#include "library/message_builder.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/elaborator_exception.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static name * g_by_name = nullptr;

expr mk_by(expr const & e) { return mk_annotation(*g_by_name, e); }
bool is_by(expr const & e) { return is_annotation(e, *g_by_name); }
expr const & get_by_arg(expr const & e) { lean_assert(is_by(e)); return get_annotation_arg(e); }

vm_obj tactic_to_expr_core(vm_obj const & qe, vm_obj const & relaxed, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx = s.mctx();
    try {
        environment env = s.env();
        auto e = to_expr(qe);
        bool recover_from_errors = false;
        elaborator elab(env, s.get_options(), s.decl_name(), mctx, g->get_context(), recover_from_errors);
        expr r = elab.elaborate(resolve_names(env, g->get_context(), e));
        if (!to_bool(relaxed))
            elab.ensure_no_unassigned_metavars(r);
        mctx = elab.mctx();
        env  = elab.env();

        r = mctx.instantiate_mvars(r);
        if (to_bool(relaxed) && has_expr_metavar(r)) {
            buffer<expr> new_goals;
            name_set found;
            for_each(r, [&](expr const & e, unsigned) {
                    if (!has_expr_metavar(e)) return false;
                    if (is_metavar_decl_ref(e) && !found.contains(mlocal_name(e))) {
                        mctx.instantiate_mvars_at_type_of(e);
                        new_goals.push_back(e);
                        found.insert(mlocal_name(e));
                    }
                    return true;
                });
            list<expr> new_gs = cons(head(s.goals()), to_list(new_goals.begin(), new_goals.end(), tail(s.goals())));
            return tactic::mk_success(to_obj(r), set_env_mctx_goals(s, env, mctx, new_gs));
        } else {
            return tactic::mk_success(to_obj(r), set_env_mctx(s, env, mctx));
        }
    } catch (elaborator_exception & ex) {
        return tactic::mk_exception(ex, s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_elaborate() {
    g_by_name           = new name("by");
    register_annotation(*g_by_name);
    DECLARE_VM_BUILTIN(name({"tactic", "to_expr"}), tactic_to_expr_core);
}

void finalize_elaborate() {
    delete g_by_name;
}
}
