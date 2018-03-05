/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {
vm_obj tactic_mk_app(vm_obj const & c, vm_obj const & as, vm_obj const & tmode, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    try {
        type_context_old ctx       = mk_type_context_for(s, to_transparency_mode(tmode));
        buffer<expr> args;
        to_buffer_expr(as, args);
        expr r                 = mk_app(ctx, to_name(c), args.size(), args.data());
        return tactic::mk_success(to_obj(r), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

#define MK_APP(CODE) {                                                  \
    tactic_state const & s = tactic::to_state(_s);                       \
    try {                                                               \
        type_context_old ctx       = mk_type_context_for(s);                \
        expr r = CODE;                                                  \
        return tactic::mk_success(to_obj(r), s);                         \
    } catch (exception & ex) {                                          \
        return tactic::mk_exception(ex, s);                              \
    }                                                                   \
}

vm_obj tactic_mk_congr_arg(vm_obj const & f, vm_obj const & H, vm_obj const & _s) {
    MK_APP(mk_congr_arg(ctx, to_expr(f), to_expr(H)));
}

vm_obj tactic_mk_congr_fun(vm_obj const & H, vm_obj const & a, vm_obj const & _s) {
    MK_APP(mk_congr_fun(ctx, to_expr(H), to_expr(a)));
}

vm_obj tactic_mk_congr(vm_obj const & H1, vm_obj const & H2, vm_obj const & _s) {
    MK_APP(mk_congr(ctx, to_expr(H1), to_expr(H2)));
}

vm_obj tactic_mk_eq_refl(vm_obj const & a, vm_obj const & _s) {
    MK_APP(mk_eq_refl(ctx, to_expr(a)));
}

vm_obj tactic_mk_eq_symm(vm_obj const & h, vm_obj const & _s) {
    MK_APP(mk_eq_symm(ctx, to_expr(h)));
}

vm_obj tactic_mk_eq_trans(vm_obj const & h1, vm_obj const & h2, vm_obj const & _s) {
    MK_APP(mk_eq_trans(ctx, to_expr(h1), to_expr(h2)));
}

vm_obj tactic_mk_eq_mpr(vm_obj const & h1, vm_obj const & h2, vm_obj const & _s) {
    MK_APP(mk_eq_mpr(ctx, to_expr(h1), to_expr(h2)));
}

vm_obj tactic_mk_eq_mp(vm_obj const & h1, vm_obj const & h2, vm_obj const & _s) {
    MK_APP(mk_eq_mp(ctx, to_expr(h1), to_expr(h2)));
}

vm_obj tactic_mk_mapp(vm_obj const & c, vm_obj const & as, vm_obj const & tmode, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    try {
        type_context_old ctx       = mk_type_context_for(s, to_transparency_mode(tmode));
        buffer<bool> mask;
        buffer<expr> args;
        vm_obj it = as;
        while (!is_nil(it)) {
            vm_obj opt = head(it);
            if (is_none(opt)) {
                mask.push_back(false);
            } else {
                mask.push_back(true);
                args.push_back(to_expr(get_some_value(opt)));
            }
            it = tail(it);
        }
        expr r = mk_app(ctx, to_name(c), mask.size(), mask.data(), args.data());
        return tactic::mk_success(to_obj(r), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_app_builder_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_app"}),        tactic_mk_app);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_mapp"}),       tactic_mk_mapp);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_congr_arg"}),  tactic_mk_congr_arg);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_congr_fun"}),  tactic_mk_congr_fun);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_congr"}),      tactic_mk_congr);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_eq_refl"}),    tactic_mk_eq_refl);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_eq_symm"}),    tactic_mk_eq_symm);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_eq_trans"}),   tactic_mk_eq_trans);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_eq_mp"}),      tactic_mk_eq_mp);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_eq_mpr"}),     tactic_mk_eq_mpr);
}

void finalize_app_builder_tactics() {
}
}
