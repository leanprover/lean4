/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
namespace lean {
static vm_obj dummy_unary_op(vm_obj const &, vm_obj const &) {
    throw exception("uint support has not been implemented in the old VM");
}

static vm_obj dummy_binary_op(vm_obj const &, vm_obj const &) {
    throw exception("uint support has not been implemented in the old VM");
}

void initialize_vm_uint() {
    DECLARE_VM_BUILTIN(name({"uint8", "of_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "to_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "add"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "sub"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "mul"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "div"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "mod"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "modn"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "dec_eq"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "dec_lt"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint8", "dec_le"}),     dummy_binary_op);

    DECLARE_VM_BUILTIN(name({"uint16", "of_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "to_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "add"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "sub"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "mul"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "div"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "mod"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "modn"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "dec_eq"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "dec_lt"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint16", "dec_le"}),     dummy_binary_op);

    DECLARE_VM_BUILTIN(name({"uint32", "of_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "to_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "add"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "sub"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "mul"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "div"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "mod"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "modn"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "dec_eq"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "dec_lt"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint32", "dec_le"}),     dummy_binary_op);

    DECLARE_VM_BUILTIN(name({"uint64", "of_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "to_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "add"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "sub"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "mul"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "div"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "mod"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "modn"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "dec_eq"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "dec_lt"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"uint64", "dec_le"}),     dummy_binary_op);

    DECLARE_VM_BUILTIN(name({"usize", "of_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"usize", "to_nat"}),     dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"usize", "add"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "sub"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "mul"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "div"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "mod"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "modn"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "dec_eq"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "dec_lt"}),     dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"usize", "dec_le"}),     dummy_binary_op);
}

void finalize_vm_uint() {
}
}
