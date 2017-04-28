/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/quote.h"
#include "library/string.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_pos_info.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/util.h"

namespace lean {
vm_obj pexpr_of_expr(vm_obj const & e) {
    return to_obj(mk_as_is(to_expr(e)));
}

vm_obj expr_to_string(vm_obj const &);

vm_obj pexpr_to_string(vm_obj const & e) {
    return expr_to_string(e);
}

vm_obj pexpr_to_raw_expr(vm_obj const & e) {
    return e;
}

vm_obj pexpr_of_raw_expr(vm_obj const & e) {
    return e;
}

vm_obj pexpr_mk_placeholder() {
    return to_obj(mk_expr_placeholder());
}

vm_obj pexpr_pos(vm_obj const & e) {
    if (auto p = get_pos_info(to_expr(e)))
        return mk_vm_some(to_obj(*p));
    return mk_vm_none();
}

vm_obj pexpr_mk_quote_macro(vm_obj const & e) {
    return to_obj(mk_quote(to_expr(e), /* is_expr */ false));
}

vm_obj pexpr_mk_prenum_macro(vm_obj const & n) {
    return to_obj(mk_prenum(is_simple(n) ? mpz{cidx(n)} : to_mpz(n)));
}

vm_obj pexpr_mk_string_macro(vm_obj const & s) {
    return to_obj(from_string(to_string(s)));
}

vm_obj pexpr_mk_explicit(vm_obj const & e) {
    return to_obj(mk_explicit(to_expr(e)));
}

vm_obj pexpr_mk_field_macro(vm_obj const & e, vm_obj const & fname) {
    return to_obj(mk_field_notation(to_expr(e), to_name(fname)));
}

void initialize_vm_pexpr() {
    DECLARE_VM_BUILTIN(name({"pexpr", "subst"}),          expr_subst);
    DECLARE_VM_BUILTIN(name({"pexpr", "of_expr"}),        pexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "to_string"}),      pexpr_to_string);
    DECLARE_VM_BUILTIN(name({"pexpr", "of_raw_expr"}),    pexpr_of_raw_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "to_raw_expr"}),    pexpr_to_raw_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "mk_placeholder"}), pexpr_mk_placeholder);

    DECLARE_VM_BUILTIN(name("pexpr", "pos"),              pexpr_pos);

    DECLARE_VM_BUILTIN(name("pexpr", "mk_quote_macro"),   pexpr_mk_quote_macro);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_prenum_macro"),  pexpr_mk_prenum_macro);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_string_macro"),  pexpr_mk_string_macro);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_explicit"),      pexpr_mk_explicit);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_field_macro"),   pexpr_mk_field_macro);
}

void finalize_vm_pexpr() {
}
}
