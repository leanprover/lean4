/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/abstract_expr.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj tactic_abstract_hash(vm_obj const & e, vm_obj const & s) {
    type_context_scope ctx(s);
    unsigned h = abstract_hash(ctx, to_expr(e)) % LEAN_MAX_SMALL_NAT;
    return mk_tactic_success(mk_vm_simple(h), to_tactic_state(s));
}

vm_obj tactic_abstract_weight(vm_obj const & e, vm_obj const & s) {
    type_context_scope ctx(s);
    unsigned h = abstract_weight(ctx, to_expr(e)) % LEAN_MAX_SMALL_NAT;
    return mk_tactic_success(mk_vm_simple(h), to_tactic_state(s));
}

vm_obj tactic_abstract_eq(vm_obj const & e1, vm_obj const & e2, vm_obj const & s) {
    type_context_scope ctx(s);
    bool r = abstract_eq(ctx, to_expr(e1), to_expr(e2));
    return mk_tactic_success(mk_vm_bool(r), to_tactic_state(s));
}

void initialize_abstract_expr_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "abstract_hash"}),   tactic_abstract_hash);
    DECLARE_VM_BUILTIN(name({"tactic", "abstract_weight"}), tactic_abstract_weight);
    DECLARE_VM_BUILTIN(name({"tactic", "abstract_eq"}),     tactic_abstract_eq);
}
void finalize_abstract_expr_tactics() {
}
}
