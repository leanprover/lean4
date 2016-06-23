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

void initialize_abstract_expr_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "abstract_hash"}), tactic_abstract_hash);
}
void finalize_abstract_expr_tactics() {
}
}
