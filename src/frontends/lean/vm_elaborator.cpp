/*
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich

TEMPORARY code for the old runtime
*/

#include <string>
#include <iostream>
#include "util/timeit.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "frontends/lean/elaborator.h"

namespace lean {
struct vm_env : public vm_external {
    environment m_env;

    explicit vm_env(environment const & env) : m_env(env) {}

    virtual ~vm_env() {}

    virtual void dealloc() override { delete this; }

    virtual vm_external *ts_clone(vm_clone_fn const &) {lean_unreachable()}

    virtual vm_external *clone(vm_clone_fn const &) {lean_unreachable()}
};

vm_obj vm_environment_empty() {
    return mk_vm_external(new vm_env(environment()));
}

name to_name(vm_obj const & o) {
    switch (cidx(o)) {
        case 0: return name();
        case 1: {
            std::string str = to_string(cfield(o, 1));
            return name(to_name(cfield(o, 0)), str.c_str());
        }
        case 2:
            return name(to_name(cfield(o, 0)), to_unsigned(cfield(o, 1)));
        default: lean_unreachable();
    }
}

level to_level(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return mk_level_zero();
        case 1:
            return mk_succ(to_level(cfield(o, 0)));
        case 2:
            return mk_max(to_level(cfield(o, 0)), to_level(cfield(o, 1)));
        case 3:
            return mk_imax(to_level(cfield(o, 0)), to_level(cfield(o, 1)));
        case 4:
            return mk_univ_param(to_name(cfield(o, 0)));
        case 5:
            return mk_univ_mvar(to_name(cfield(o, 0)));
        default: lean_unreachable();
    }
}

levels to_levels(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return levels();
        case 1:
            return levels(to_level(cfield(o, 0)), to_levels(cfield(o, 1)));
        default: lean_unreachable();
    }
}

binder_info to_binder_info(vm_obj const & o) {
    lean_assert(is_simple(o));
    return static_cast<binder_info>(cidx(o));
}

kvmap to_kvmap(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return kvmap();
        case 1: {
            auto vm_k = cfield(cfield(o, 0), 0);
            auto vm_v = cfield(cfield(o, 0), 1);
            auto vm_d = cfield(vm_v, 0);
            data_value v;
            switch (cidx(vm_v)) {
                case 0:
                    v = data_value(to_string(vm_d));
                    break;
                case 1:
                    v = data_value(nat(vm_nat_to_mpz1(vm_d)));
                    break;
                case 2:
                    v = data_value(to_bool(vm_d));
                    break;
                case 3:
                    v = data_value(to_name(vm_d));
                    break;
                default: lean_unreachable();
            }
            return kvmap({to_name(vm_k), v}, to_kvmap(cfield(o, 1)));
        }
        default: lean_unreachable();
    }
}

expr to_expr(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return mk_bvar(nat(vm_nat_to_mpz1(cfield(o, 0))));
        case 1:
            return mk_local(to_name(cfield(o, 0)), to_name(cfield(o, 0)), expr(), mk_binder_info());
        case 2:
            return mk_metavar(to_name(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 3:
            return mk_sort(to_level(cfield(o, 0)));
        case 4:
            return mk_constant(to_name(cfield(o, 0)), to_levels(cfield(o, 1)));
        case 5:
            return mk_app(to_expr(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 6:
            return mk_lambda(to_name(cfield(o, 0)), to_expr(cfield(o, 1)), to_expr(cfield(o, 2)),
                             to_binder_info(cfield(o, 3)));
        case 7:
            return mk_pi(to_name(cfield(o, 0)), to_expr(cfield(o, 1)), to_expr(cfield(o, 2)),
                         to_binder_info(cfield(o, 3)));
        case 8:
            return mk_let(to_name(cfield(o, 0)), to_expr(cfield(o, 1)), to_expr(cfield(o, 2)), to_expr(cfield(o, 3)));
        case 9: {
            auto l = cfield(o, 0);
            switch (cidx(l)) {
                case 0:
                    return mk_lit(literal(to_string(cfield(l, 0)).c_str()));
                case 1:
                    return mk_lit(literal(vm_nat_to_mpz1(cfield(l, 0))));
                default: lean_unreachable();
            }
        }
        case 10:
            return mk_mdata(to_kvmap(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 11:
            return mk_proj(to_name(cfield(o, 0)), nat(vm_nat_to_mpz1(cfield(o, 1))), to_expr(cfield(o, 2)));
        default: lean_unreachable();
    }
}

/* elaborate_command : expr -> environment -> except string environment */
// TODO(Sebastian): replace `string` with `message` in the new runtime
vm_obj vm_elaborate_command(vm_obj const & vm_cmd, vm_obj const & vm_e) {
    lean_vm_check(dynamic_cast<vm_env *>(to_external(vm_e)));
    auto env = static_cast<vm_env *>(to_external(vm_e))->m_env;

    try {
        env = elaborate_command(env, to_expr(vm_cmd));
        return mk_vm_constructor(1, mk_vm_external(new vm_env(env)));
    } catch (exception & e) {
        return mk_vm_constructor(0, to_obj(e.what()));
    }
}

void initialize_vm_elaborator() {
    DECLARE_VM_BUILTIN(name({"lean", "environment", "empty"}), vm_environment_empty);
    DECLARE_VM_BUILTIN(name({"lean", "elaborator", "elaborate_command"}), vm_elaborate_command);
}

void finalize_vm_elaborator() {
}
}
