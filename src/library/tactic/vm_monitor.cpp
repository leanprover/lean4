/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <string>
#include "library/vm/vm.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj _vm_monitor_register(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    LEAN_TACTIC_TRY;
    return mk_tactic_success(set_env(s, vm_monitor_register(s.env(), n)));
    LEAN_TACTIC_CATCH(s);
}

vm_obj vm_core_map(vm_obj const &, vm_obj const &, vm_obj const & fn, vm_obj const & a, vm_obj const & s) {
    vm_obj v = invoke(a, s);
    return invoke(fn, v);
}

vm_obj vm_core_ret(vm_obj const &, vm_obj const & a, vm_obj const & /* s */) {
    return a;
}

vm_obj vm_core_bind(vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & b, vm_obj const & s) {
    return invoke(b, invoke(a, s), s);
}

struct vm_vm_decl : public vm_external {
    vm_decl m_val;
    vm_vm_decl(vm_decl const & v):m_val(v) {}
    virtual ~vm_vm_decl() {}
    virtual void dealloc() override { this->~vm_vm_decl(); get_vm_allocator().deallocate(sizeof(vm_vm_decl), this); }
};

vm_decl const & to_vm_decl(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_vm_decl*>(to_external(o)));
    return static_cast<vm_vm_decl*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_decl const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_vm_decl))) vm_vm_decl(e));
}

/*
inductive vm_decl_kind
| bytecode | builtin | cfun
*/
vm_obj _vm_decl_kind(vm_obj const & d) {
    switch (to_vm_decl(d).kind()) {
    case vm_decl_kind::Bytecode: return mk_vm_simple(0);
    case vm_decl_kind::Builtin:  return mk_vm_simple(1);
    case vm_decl_kind::CFun:     return mk_vm_simple(2);
    }
    lean_unreachable();
}

vm_obj vm_decl_to_name(vm_obj const & d) {
    return to_obj(to_vm_decl(d).get_name());
}

vm_obj vm_decl_idx(vm_obj const & d) {
    return mk_vm_nat(to_vm_decl(d).get_idx());
}

vm_obj vm_decl_arity(vm_obj const & d) {
    return mk_vm_nat(to_vm_decl(d).get_arity());
}

vm_obj vm_decl_pos(vm_obj const & d) {
    if (optional<pos_info> pos = to_vm_decl(d).get_pos_info())
        return mk_vm_some(mk_vm_pair(mk_vm_nat(pos->first), mk_vm_nat(pos->second)));
    else
        return mk_vm_none();
}

vm_obj vm_decl_olean(vm_obj const & d) {
    if (optional<std::string> olean = to_vm_decl(d).get_olean())
        return mk_vm_some(to_obj(*olean));
    else
        return mk_vm_none();
}

vm_obj vm_decl_args_info(vm_obj const & d) {
    return to_vm_list(to_vm_decl(d).get_args_info(),
                      [](vm_local_info const & info) {
                          return mk_vm_pair(to_obj(info.first), to_obj(info.second));
                      });
}

static vm_obj mk_vm_success(vm_obj const & o) {
    return mk_vm_some(o);
}

static vm_obj mk_vm_failure() {
    return mk_vm_none();
}

vm_obj vm_get_decl(vm_obj const & n, vm_obj const & /*s*/) {
    if (optional<vm_decl> d = get_vm_state_being_debugged().get_decl(to_name(n)))
        return mk_vm_success(to_obj(*d));
    else
        return mk_vm_failure();
}

vm_obj vm_stack_size(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().stack_size()));
}

vm_obj vm_stack_obj(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx = force_to_unsigned(i, std::numeric_limits<unsigned>::max());
    if (idx >= vm.stack_size()) return mk_vm_failure();
    return mk_vm_success(vm.get_core(idx));
}

vm_obj vm_stack_obj_info(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx    = force_to_unsigned(i, std::numeric_limits<unsigned>::max());
    vm_local_info info = vm.get_info(idx);
    return mk_vm_success(mk_vm_pair(to_obj(info.first), to_obj(info.second)));
}

vm_obj vm_call_stack_size(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().call_stack_size()));
}

vm_obj vm_call_stack_fn(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx = force_to_unsigned(i, std::numeric_limits<unsigned>::max());
    if (idx >= vm.call_stack_size()) return mk_vm_failure();
    return mk_vm_success(to_obj(vm.call_stack_fn(idx)));
}

vm_obj vm_bp(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().bp()));
}

vm_obj vm_pc(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().pc()));
}

vm_obj vm_curr_fn(vm_obj const & /*s*/) {
    return mk_vm_success(to_obj(get_vm_state_being_debugged().curr_fn()));
}

void initialize_vm_monitor() {
    DECLARE_VM_BUILTIN(name({"vm_monitor", "register"}),  _vm_monitor_register);
    DECLARE_VM_BUILTIN(name({"vm_core", "map"}),        vm_core_map);
    DECLARE_VM_BUILTIN(name({"vm_core", "ret"}),        vm_core_ret);
    DECLARE_VM_BUILTIN(name({"vm_core", "bind"}),       vm_core_bind);
    DECLARE_VM_BUILTIN(name({"vm_decl", "kind"}),       _vm_decl_kind);
    DECLARE_VM_BUILTIN(name({"vm_decl", "to_name"}),    vm_decl_to_name);
    DECLARE_VM_BUILTIN(name({"vm_decl", "idx"}),        vm_decl_idx);
    DECLARE_VM_BUILTIN(name({"vm_decl", "arity"}),      vm_decl_arity);
    DECLARE_VM_BUILTIN(name({"vm_decl", "pos"}),        vm_decl_pos);
    DECLARE_VM_BUILTIN(name({"vm_decl", "olean"}),      vm_decl_olean);
    DECLARE_VM_BUILTIN(name({"vm_decl", "args_info"}),  vm_decl_args_info);
    DECLARE_VM_BUILTIN(name({"vm", "get_decl"}),        vm_get_decl);
    DECLARE_VM_BUILTIN(name({"vm", "stack_size"}),      vm_stack_size);
    DECLARE_VM_BUILTIN(name({"vm", "stack_obj"}),       vm_stack_obj);
    DECLARE_VM_BUILTIN(name({"vm", "stack_obj_info"}),  vm_stack_obj_info);
    DECLARE_VM_BUILTIN(name({"vm", "call_stack_size"}), vm_call_stack_size);
    DECLARE_VM_BUILTIN(name({"vm", "call_stack_fn"}),   vm_call_stack_fn);
    DECLARE_VM_BUILTIN(name({"vm", "bp"}),              vm_bp);
    DECLARE_VM_BUILTIN(name({"vm", "pc"}),              vm_pc);
    DECLARE_VM_BUILTIN(name({"vm", "curr_fn"}),         vm_curr_fn);
}

void finalize_vm_monitor() {
}
}
