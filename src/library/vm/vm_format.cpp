/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/sexpr/format.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"

namespace lean {
struct vm_format : public vm_external {
    format m_val;
    vm_format(format const & v):m_val(v) {}
    virtual ~vm_format() {}
};

format const & to_format(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_format*>(to_external(o)));
    return static_cast<vm_format*>(to_external(o))->m_val;
}

vm_obj to_obj(format const & n) {
    return mk_vm_external(new vm_format(n));
}

vm_obj format_line() {
    return to_obj(line());
}

vm_obj format_space() {
    return to_obj(space());
}

vm_obj format_compose(vm_obj const & fmt1, vm_obj const & fmt2) {
    return to_obj(compose(to_format(fmt1), to_format(fmt2)));
}

vm_obj format_nest(vm_obj const & i, vm_obj const & fmt) {
    return to_obj(nest(to_unsigned(i), to_format(fmt)));
}

vm_obj format_highlight(vm_obj const & fmt, vm_obj const & c) {
    return to_obj(highlight(to_format(fmt), static_cast<format::format_color>(cidx(c))));
}

vm_obj format_group(vm_obj const & fmt) {
    return to_obj(group(to_format(fmt)));
}

vm_obj format_of_string(vm_obj const & s) {
    return to_obj(format(to_string(s)));
}

vm_obj format_of_nat(vm_obj const & n) {
    if (is_simple(n))
        return to_obj(format(cidx(n)));
    else
        return to_obj(format(to_mpz(n)));
}

vm_obj format_flatten(vm_obj const & fmt) {
    return to_obj(flatten(to_format(fmt)));
}

vm_obj format_to_string(vm_obj const & fmt, vm_obj const & opts) {
    std::ostringstream out;
    out << mk_pair(to_format(fmt), to_options(opts));
    return to_obj(out.str());
}

vm_obj format_print_using(vm_obj const & fmt, vm_obj const & opts, vm_obj const &) {
    std::cout << mk_pair(to_format(fmt), to_options(opts));
    return mk_vm_unit();
}

vm_obj format_of_options(vm_obj const & opts) {
    return to_obj(pp(to_options(opts)));
}

void initialize_vm_format() {
    DECLARE_VM_BUILTIN(name({"format", "line"}),             format_line);
    DECLARE_VM_BUILTIN(name({"format", "space"}),            format_space);
    DECLARE_VM_BUILTIN(name({"format", "compose"}),          format_compose);
    DECLARE_VM_BUILTIN(name({"format", "nest"}),             format_nest);
    DECLARE_VM_BUILTIN(name({"format", "highlight"}),        format_highlight);
    DECLARE_VM_BUILTIN(name({"format", "group"}),            format_group);
    DECLARE_VM_BUILTIN(name({"format", "of_string"}),        format_of_string);
    DECLARE_VM_BUILTIN(name({"format", "of_nat"}),           format_of_nat);
    DECLARE_VM_BUILTIN(name({"format", "flatten"}),          format_flatten);
    DECLARE_VM_BUILTIN(name({"format", "to_string"}),        format_to_string);
    DECLARE_VM_BUILTIN(name({"format", "print_using"}),      format_print_using);
    DECLARE_VM_BUILTIN(name({"format", "of_options"}),       format_of_options);
}

void finalize_vm_format() {
}
}
