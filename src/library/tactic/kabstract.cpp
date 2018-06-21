/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/module.h"
#include "library/head_map.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/occurrences.h"
#include "library/tactic/tactic_state.h"

namespace lean {
expr kabstract(type_context_old & ctx, expr const & e, expr const & t, occurrences const & occs, bool unify) {
    lean_assert(!has_loose_bvars(e));
    head_index idx1(t);
    unsigned i = 1;
    unsigned t_nargs = get_app_num_args(t);
    return replace(e, [&](expr const & s, unsigned offset) {
            if (!has_loose_bvars(s)) {
                head_index idx2(s);
                if (idx1.kind() == idx2.kind() &&
                    idx1.get_name() == idx2.get_name() &&
                    /* fail if same function application and different number of arguments */
                    (idx1.get_name() != idx2.get_name() || t_nargs == get_app_num_args(s)) &&
                    ((unify && ctx.unify(t, s)) || (!unify && ctx.match(t, s)))) {
                    if (occs.contains(i)) {
                        lean_trace("kabstract", scope_trace_env _(ctx.env(), ctx);
                                   tout() << "found target:\n" << s << "\n";);
                        i++;
                        return some_expr(mk_bvar(offset));
                    } else {
                        i++;
                    }
                }
            }
            return none_expr();
        }, occs.is_all());
}

bool kdepends_on(type_context_old & ctx, expr const & e, expr const & t) {
    bool found = false;
    head_index idx1(t);
    unsigned t_nargs = get_app_num_args(t);
    for_each(e, [&](expr const & s, unsigned) {
            if (found) return false;
            if (!has_loose_bvars(s)) {
                head_index idx2(s);
                if (idx1.kind() == idx2.kind() &&
                    idx1.get_name() == idx2.get_name() &&
                    /* fail if same function application and different number of arguments */
                    (idx1.get_name() != idx2.get_name() || t_nargs == get_app_num_args(s)) &&
                    ctx.is_def_eq(t, s)) {
                    found = true; return false;
                }
            }
            return true;
        });
    return found;
}

vm_obj tactic_kdepends_on(vm_obj const & e, vm_obj const & t, vm_obj const & md, vm_obj const & s) {
    try {
        type_context_old ctx = mk_type_context_for(s, md);
        return tactic::mk_success(mk_vm_bool(kdepends_on(ctx, to_expr(e), to_expr(t))), tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(std::current_exception(), tactic::to_state(s));
    }
}

vm_obj tactic_kabstract(vm_obj const & e, vm_obj const & t, vm_obj const & md, vm_obj const & u, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    try {
        type_context_old ctx = mk_type_context_for(s, to_transparency_mode(md));
        auto a = kabstract(ctx, to_expr(e), to_expr(t), occurrences(), to_bool(u));
        return tactic::mk_success(to_obj(a), set_mctx(s, ctx.mctx()));
    } catch (exception & ex) {
        return tactic::mk_exception(std::current_exception(), s);
    }
}

void initialize_kabstract() {
    register_trace_class("kabstract");
    DECLARE_VM_BUILTIN(name({"tactic", "kdepends_on"}), tactic_kdepends_on);
    DECLARE_VM_BUILTIN(name("tactic", "kabstract"),     tactic_kabstract);
}

void finalize_kabstract() {
}
}
