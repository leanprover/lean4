/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>
#include <fstream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_format.h"
#include "library/native_compiler/native_compiler.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/nat_value.h"

namespace lean {

vm_obj native_is_internal_cnstr(vm_obj const & e) {
    auto opt_unsigned = is_internal_cnstr(to_expr(e));
    if (opt_unsigned) {
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_is_internal_cases(vm_obj const & e) {
    auto opt_unsigned = is_internal_cases(to_expr(e));
    if (opt_unsigned) {
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_is_internal_proj(vm_obj const & e) {
    auto opt_unsigned = is_internal_proj(to_expr(e));
    if (opt_unsigned) {
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_get_nat_value(vm_obj const & o) {
    expr e = to_expr(o);
    if (is_nat_value(e)) {
        auto n = mk_vm_nat(get_nat_value_value(e));
        return mk_vm_constructor(1, { n });
    } else {
        return mk_vm_simple(0);
    }
}

vm_obj native_get_builtin(vm_obj const & o) {
    name n = to_name(o);

    if (!get_vm_builtin_internal_name(n)) {
        return mk_vm_none();
    }

    switch (get_vm_builtin_kind(n)) {
        case vm_builtin_kind::VMFun: {
            name internal_name = name(get_vm_builtin_internal_name(n));
            auto b = mk_vm_constructor(2, { to_obj(internal_name) });
            return mk_vm_some(b);
        }
        case vm_builtin_kind::CFun: {
            auto efn = *get_builtin(n);
            auto pair = mk_vm_constructor(0, { to_obj(efn.m_name), mk_vm_simple(efn.m_arity) });
            return mk_vm_some(pair);
        }
        case vm_builtin_kind::Cases: {
            auto efn = *get_builtin(n);
            auto pair = mk_vm_constructor(1, { to_obj(efn.m_name), mk_vm_simple(efn.m_arity) });
            return mk_vm_some(pair);
        }
        default:
            return mk_vm_none();
    }
}

vm_obj native_dump_format(vm_obj const & string_obj, vm_obj const & format_obj) {
    auto file_path = to_string(string_obj);
    auto fmt = to_format(format_obj);

    std::fstream dump_file(file_path, std::ios_base::out);
    pretty(dump_file, 80, true, fmt);

    dump_file.close();

    return mk_vm_nat(0);
}

void initialize_vm_native() {
    // Not sure if we should expose ese or what?
    DECLARE_VM_BUILTIN(name({"native", "is_internal_cnstr"}), native_is_internal_cnstr);
    DECLARE_VM_BUILTIN(name({"native", "is_internal_cases"}), native_is_internal_cases);
    DECLARE_VM_BUILTIN(name({"native", "is_internal_proj"}), native_is_internal_proj);
    DECLARE_VM_BUILTIN(name({"native", "get_nat_value"}), native_get_nat_value);
    DECLARE_VM_BUILTIN(name({"native", "get_builtin"}), native_get_builtin);
    DECLARE_VM_BUILTIN(name({"native", "dump_format"}), native_dump_format);
}

void finalize_vm_native() {
}
}
