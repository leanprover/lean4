 /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <string>
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "library/io_state.h"
#include "library/util.h"
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_pos_info.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"

namespace lean {
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

/*
inductive vm_obj_kind
| simple | constructor | closure | mpz
| name | level | expr | declaration
| environment | tactic_state | format
| options | other
*/
vm_obj _vm_obj_kind(vm_obj const & o) {
    switch (o.kind()) {
    case vm_obj_kind::Simple: return mk_vm_simple(0);
    case vm_obj_kind::Constructor: return mk_vm_simple(1);
    case vm_obj_kind::Closure: return mk_vm_simple(2);
    case vm_obj_kind::NativeClosure: return mk_vm_simple(3);
    case vm_obj_kind::MPZ: return mk_vm_simple(4);
    case vm_obj_kind::External:
        if (is_name(o)) return mk_vm_simple(5);
        else if (is_level(o)) return mk_vm_simple(6);
        else if (is_expr(o)) return mk_vm_simple(7);
        else if (is_declaration(o)) return mk_vm_simple(8);
        else if (is_env(o)) return mk_vm_simple(9);
        else if (tactic::is_state(o)) return mk_vm_simple(10);
        else if (is_format(o)) return mk_vm_simple(11);
        else if (is_options(o)) return mk_vm_simple(12);
        else return mk_vm_simple(13);
    }
    lean_unreachable();
}

vm_obj vm_obj_cidx(vm_obj const & o) {
    switch (o.kind()) {
    case vm_obj_kind::Simple:
    case vm_obj_kind::Constructor:
        return mk_vm_nat(cidx(o));
    default:
        return mk_vm_nat(0);
    }
}

vm_obj vm_obj_fn_idx(vm_obj const & o) {
    switch (o.kind()) {
    case vm_obj_kind::Closure:
        return mk_vm_nat(cfn_idx(o));
    default:
        return mk_vm_nat(0);
    }
}

vm_obj vm_obj_fields(vm_obj const & o) {
    switch (o.kind()) {
    case vm_obj_kind::Constructor: {
        unsigned i = csize(o);
        vm_obj r   = mk_vm_simple(0);
        while (i > 0) {
            --i;
            r = mk_vm_constructor(1, cfield(o, i), r);
        }
        return r;
    }
    default:
        return mk_vm_simple(0);
    }
}

vm_obj vm_obj_to_nat(vm_obj const & o) {
    switch (o.kind()) {
    case vm_obj_kind::Simple:
    case vm_obj_kind::MPZ:
        return o;
    default:
        return mk_vm_nat(0);
    }
}

vm_obj vm_obj_to_name(vm_obj const & o) {
    if (is_name(o))
        return o;
    else
        return to_obj(name());
}

vm_obj vm_obj_to_level(vm_obj const & o) {
    if (is_level(o))
        return o;
    else
        return to_obj(level());
}

vm_obj vm_obj_to_expr(vm_obj const & o) {
    if (is_expr(o))
        return o;
    else
        return to_obj(expr());
}

vm_obj vm_obj_to_declaration(vm_obj const & o) {
    if (is_declaration(o))
        return o;
    else
        return to_obj(declaration());
}

vm_obj vm_obj_to_environment(vm_obj const & o) {
    if (is_env(o))
        return o;
    else
        return to_obj(environment());
}

vm_obj vm_obj_to_tactic_state(vm_obj const & o) {
    if (tactic::is_state(o))
        return o;
    else
        return to_obj(mk_tactic_state_for(environment(), options(), {}, local_context(), mk_Prop()));
}

vm_obj vm_obj_to_format(vm_obj const & o) {
    if (is_format(o))
        return o;
    else
        return to_obj(format());
}

struct vm_vm_decl : public vm_external {
    vm_decl m_val;
    vm_vm_decl(vm_decl const & v):m_val(v) {}
    virtual ~vm_vm_decl() {}
    virtual void dealloc() override { this->~vm_vm_decl(); get_vm_allocator().deallocate(sizeof(vm_vm_decl), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_vm_decl(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_vm_decl))) vm_vm_decl(m_val); }
};

vm_decl const & to_vm_decl(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_vm_decl*>(to_external(o)));
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
        return mk_vm_some(to_obj(*pos));
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
    unsigned idx = force_to_unsigned(i);
    if (idx >= vm.stack_size()) return mk_vm_failure();
    return mk_vm_success(vm.get_core(idx));
}

vm_obj vm_stack_obj_info(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx    = force_to_unsigned(i);
    vm_local_info info = vm.get_info(idx);
    return mk_vm_success(mk_vm_pair(to_obj(info.first), to_obj(info.second)));
}

static format default_format(vm_state const & vm, unsigned idx) {
    lean_assert(idx < vm.stack_size());
    vm_obj o = vm.get_core(idx);
    vm_local_info info = vm.get_info(idx);
    if (auto type = info.second) {
        try {
            vm_state & curr_vm = get_vm_state();
            type_context_old ctx(curr_vm.env());
            level u = get_level(ctx, *type);
            expr has_to_format = mk_app(mk_constant(get_has_to_format_name(), {u}), *type);
            if (optional<expr> instance = ctx.mk_class_instance(has_to_format)) {
                environment aux_env = curr_vm.env();
                /* type -> format */
                expr aux_type  = mk_arrow(*type, mk_constant(get_format_name()));
                /* (@to_fmt type *instance) */
                expr aux_value = mk_app(mk_constant(get_to_fmt_name(), {u}), *type, *instance);
                name aux_name  = mk_unused_name(aux_env, "_to_fmt_obj");
                auto cd = check(aux_env, mk_definition(aux_env, aux_name, {}, aux_type, aux_value, true, false));
                aux_env = aux_env.add(cd);
                aux_env = vm_compile(aux_env, aux_env.get(aux_name));
                curr_vm.update_env(aux_env);
                vm_obj fn = curr_vm.get_constant(aux_name);
                vm_obj r  = invoke(fn, o);
                lean_assert(is_format(r));
                return to_format(r);
            }
        } catch (exception &) {
        }
    }
    std::ostringstream out;
    get_vm_state_being_debugged().display(out, o);
    return format(out.str());
}

vm_obj vm_pp_stack_obj(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx = force_to_unsigned(i);
    if (idx >= vm.stack_size()) return mk_vm_failure();
    vm_obj o = vm.get_core(idx);

    format r;
    if (is_expr(o)) {
        formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
        type_context_old ctx(vm.env());
        formatter fmt                  = fmtf(vm.env(), vm.get_options(), ctx);
        try {
            r = fmt(to_expr(o));
        } catch (exception &) {
            r = default_format(vm, idx);
        }
    } else if (tactic::is_state(o)) {
        r = tactic::to_state(o).pp_core();
    } else if (is_env(o)) {
        r = format("[environment]");
    } else {
        r = default_format(vm, idx);
    }
    return mk_vm_success(to_obj(r));
}

vm_obj vm_call_stack_size(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().call_stack_size()));
}

vm_obj vm_call_stack_fn(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx = force_to_unsigned(i);
    if (idx >= vm.call_stack_size()) return mk_vm_failure();
    return mk_vm_success(to_obj(vm.call_stack_fn(idx)));
}

vm_obj vm_call_stack_var_range(vm_obj const & i, vm_obj const & /*s*/) {
    auto const & vm = get_vm_state_being_debugged();
    unsigned idx = force_to_unsigned(i);
    unsigned csz = vm.call_stack_size();
    if (idx >= csz) {
        return mk_vm_failure();
    } else {
        lean_assert(csz > 0);
        unsigned start, end;
        if (idx == csz - 1) {
            start = vm.bp();
            end   = vm.stack_size();
        } else if (idx == csz - 2) {
            start = vm.call_stack_bp(csz - 1);
            end   = vm.bp();
        } else {
            lean_assert(idx < csz - 2);
            start = vm.call_stack_bp(idx + 1);
            end   = vm.call_stack_bp(idx + 2);
        }
        return mk_vm_success(mk_vm_pair(mk_vm_nat(start), mk_vm_nat(end)));
    }
}

vm_obj vm_bp(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().bp()));
}

vm_obj vm_pc(vm_obj const & /*s*/) {
    return mk_vm_success(mk_vm_nat(get_vm_state_being_debugged().pc()));
}

vm_obj vm_get_options(vm_obj const & /*s*/) {
    return mk_vm_success(to_obj(get_vm_state_being_debugged().get_options()));
}

vm_obj vm_curr_fn(vm_obj const & /*s*/) {
    if (auto fn = get_vm_state_being_debugged().curr_fn()) {
        return mk_vm_success(to_obj(*fn));
    } else {
        return mk_vm_failure();
    }
}

vm_obj vm_obj_to_string(vm_obj const & o, vm_obj const & /*s*/) {
    std::ostringstream out;
    get_vm_state_being_debugged().display(out, o);
    return mk_vm_success(to_obj(out.str()));
}

vm_obj vm_put_str(vm_obj const & str, vm_obj const &) {
    get_global_ios().get_regular_stream() << to_string(str);
    return mk_vm_success(mk_vm_unit());
}

vm_obj vm_get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        return mk_vm_failure();
    std::string str;
    std::getline(std::cin, str);
    return mk_vm_success(to_obj(str));
}

vm_obj vm_eof(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        return mk_vm_failure();
    return mk_vm_success(mk_vm_bool(std::cin.eof()));
}

vm_obj vm_get_env(vm_obj const &) {
    return mk_vm_success(to_obj(get_vm_state_being_debugged().env()));
}

vm_obj vm_get_attribute(vm_obj const & vm_n, vm_obj const &) {
    auto const & n = to_name(vm_n);
    buffer<name> b;
    try {
        environment const & env = get_vm_state_being_debugged().env();
        get_attribute(env, n).get_instances(env, b);
        return mk_vm_success(to_obj(b));
    } catch (exception &) {
        return mk_vm_failure();
    }
}

vm_obj vm_pp_expr(vm_obj const & e, vm_obj const &) {
    auto const & vm = get_vm_state_being_debugged();
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    type_context_old ctx(vm.env());
    formatter fmt                  = fmtf(vm.env(), vm.get_options(), ctx);
    try {
        return mk_vm_success(to_obj(fmt(to_expr(e))));
    } catch (exception &) {
        std::ostringstream out;
        out << to_expr(e);
        return mk_vm_success(to_obj(format(out.str())));
    }
}

void initialize_vm_monitor() {
    register_system_attribute(basic_attribute(
            "vm_monitor", "Registers a new virtual machine monitor. The annotated definition must be the of type "
                    "`vm_monitor S`. The command will override the last monitor.",
            [](environment const & env, io_state const &, name const & n, unsigned, bool /* persistent */) {
                /* Remark: We are currently ignoring the 'local' (i.e., persistent == false) modifier */
                return vm_monitor_register(env, n);
            }));

    DECLARE_VM_BUILTIN(name({"vm_core", "map"}),             vm_core_map);
    DECLARE_VM_BUILTIN(name({"vm_core", "ret"}),             vm_core_ret);
    DECLARE_VM_BUILTIN(name({"vm_core", "bind"}),            vm_core_bind);
    DECLARE_VM_BUILTIN(name({"vm_obj", "kind"}),             _vm_obj_kind);
    DECLARE_VM_BUILTIN(name({"vm_obj", "cidx"}),             vm_obj_cidx);
    DECLARE_VM_BUILTIN(name({"vm_obj", "fn_idx"}),           vm_obj_fn_idx);
    DECLARE_VM_BUILTIN(name({"vm_obj", "fields"}),           vm_obj_fields);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_nat"}),           vm_obj_to_nat);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_name"}),          vm_obj_to_name);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_level"}),         vm_obj_to_level);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_expr"}),          vm_obj_to_expr);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_declaration"}),   vm_obj_to_declaration);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_environment"}),   vm_obj_to_environment);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_tactic_state"}),  vm_obj_to_tactic_state);
    DECLARE_VM_BUILTIN(name({"vm_obj", "to_format"}),        vm_obj_to_format);
    DECLARE_VM_BUILTIN(name({"vm_decl", "kind"}),            _vm_decl_kind);
    DECLARE_VM_BUILTIN(name({"vm_decl", "to_name"}),         vm_decl_to_name);
    DECLARE_VM_BUILTIN(name({"vm_decl", "idx"}),             vm_decl_idx);
    DECLARE_VM_BUILTIN(name({"vm_decl", "arity"}),           vm_decl_arity);
    DECLARE_VM_BUILTIN(name({"vm_decl", "pos"}),             vm_decl_pos);
    DECLARE_VM_BUILTIN(name({"vm_decl", "olean"}),           vm_decl_olean);
    DECLARE_VM_BUILTIN(name({"vm_decl", "args_info"}),       vm_decl_args_info);
    DECLARE_VM_BUILTIN(name({"vm", "get_env"}),              vm_get_env);
    DECLARE_VM_BUILTIN(name({"vm", "get_decl"}),             vm_get_decl);
    DECLARE_VM_BUILTIN(name({"vm", "stack_size"}),           vm_stack_size);
    DECLARE_VM_BUILTIN(name({"vm", "stack_obj"}),            vm_stack_obj);
    DECLARE_VM_BUILTIN(name({"vm", "stack_obj_info"}),       vm_stack_obj_info);
    DECLARE_VM_BUILTIN(name({"vm", "call_stack_size"}),      vm_call_stack_size);
    DECLARE_VM_BUILTIN(name({"vm", "call_stack_fn"}),        vm_call_stack_fn);
    DECLARE_VM_BUILTIN(name({"vm", "call_stack_var_range"}), vm_call_stack_var_range);
    DECLARE_VM_BUILTIN(name({"vm", "bp"}),                   vm_bp);
    DECLARE_VM_BUILTIN(name({"vm", "pc"}),                   vm_pc);
    DECLARE_VM_BUILTIN(name({"vm", "curr_fn"}),              vm_curr_fn);
    DECLARE_VM_BUILTIN(name({"vm", "get_options"}),          vm_get_options);
    DECLARE_VM_BUILTIN(name({"vm", "obj_to_string"}),        vm_obj_to_string);
    DECLARE_VM_BUILTIN(name({"vm", "pp_stack_obj"}),         vm_pp_stack_obj);
    DECLARE_VM_BUILTIN(name({"vm", "pp_expr"}),              vm_pp_expr);
    DECLARE_VM_BUILTIN(name({"vm", "put_str"}),              vm_put_str);
    DECLARE_VM_BUILTIN(name({"vm", "get_line"}),             vm_get_line);
    DECLARE_VM_BUILTIN(name({"vm", "eof"}),                  vm_eof);
    DECLARE_VM_BUILTIN(name({"vm", "get_attribute"}),        vm_get_attribute);
}

void finalize_vm_monitor() {
}
}
