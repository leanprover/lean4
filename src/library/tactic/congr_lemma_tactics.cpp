/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/congr_lemma.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj to_obj(congr_arg_kind k) {
    return mk_vm_simple(static_cast<unsigned>(k));
}

vm_obj to_obj(list<congr_arg_kind> const & ls) {
    return to_vm_list(ls, [&](congr_arg_kind const & k) { return to_obj(k); });
}

/*
 structure congr_lemma :=
 (type : expr) (proof : expr) (arg_kids : list congr_arg_kind)
*/
vm_obj to_obj(congr_lemma const & c) {
    return mk_vm_constructor(0, to_obj(c.get_type()), to_obj(c.get_proof()), to_obj(c.get_arg_kinds()));
}

static vm_obj mk_result(optional<congr_lemma> const & l, vm_obj const & s) {
    if (l)
        return tactic::mk_success(to_obj(*l), tactic::to_state(s));
    else
        return tactic::mk_exception("failed to generate congruence lemma, "
                                   "use 'set_option trace.congr_lemma true' to obtain additional information",
                                   tactic::to_state(s));
}

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(tactic::to_state(s))

vm_obj tactic_mk_congr_lemma_simp(vm_obj const & fn, vm_obj const & nargs, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    if (is_none(nargs)) {
        return mk_result(mk_congr_simp(ctx, to_expr(fn)), s);
    } else {
        return mk_result(mk_congr_simp(ctx, to_expr(fn), force_to_unsigned(get_some_value(nargs), 0)), s);
    }
    CATCH;
}

vm_obj tactic_mk_specialized_congr_lemma_simp(vm_obj const & a, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    return mk_result(mk_specialized_congr_simp(ctx, to_expr(a)), s);
    CATCH;
}

vm_obj tactic_mk_congr_lemma(vm_obj const & fn, vm_obj const & nargs, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    if (is_none(nargs)) {
        return mk_result(mk_congr(ctx, to_expr(fn)), s);
    } else {
        return mk_result(mk_congr(ctx, to_expr(fn), force_to_unsigned(get_some_value(nargs), 0)), s);
    }
    CATCH;
}

vm_obj tactic_mk_specialized_congr_lemma(vm_obj const & a, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    return mk_result(mk_specialized_congr(ctx, to_expr(a)), s);
    CATCH;
}

vm_obj tactic_mk_hcongr_lemma(vm_obj const & fn, vm_obj const & nargs, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    if (is_none(nargs)) {
        return mk_result(mk_hcongr(ctx, to_expr(fn)), s);
    } else {
        return mk_result(mk_hcongr(ctx, to_expr(fn), force_to_unsigned(get_some_value(nargs), 0)), s);
    }
    CATCH;
}

void initialize_congr_lemma_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_congr_lemma_simp"}),             tactic_mk_congr_lemma_simp);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_specialized_congr_lemma_simp"}), tactic_mk_specialized_congr_lemma_simp);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_congr_lemma"}),                  tactic_mk_congr_lemma);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_specialized_congr_lemma"}),      tactic_mk_specialized_congr_lemma);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_hcongr_lemma"}),                 tactic_mk_hcongr_lemma);
}

void finalize_congr_lemma_tactics() {
}
}
