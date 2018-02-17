/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include <string>
#include <algorithm>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <iomanip>
#include "util/timeit.h"
#include "util/flet.h"
#include "util/interrupt.h"
#include "util/sstream.h"
#include "util/small_object_allocator.h"
#include "util/sexpr/option_declarations.h"
#include "util/shared_mutex.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/private.h"
#include "library/profiling.h"
#include "library/util.h"
#include "library/time_task.h"
#include "library/vm/vm.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_expr.h"
#include "library/normalize.h"

#ifndef LEAN_DEFAULT_PROFILER_FREQ
#define LEAN_DEFAULT_PROFILER_FREQ 1
#endif

namespace lean {
/* Reference to the VM that is currently running. */
LEAN_THREAD_VALUE(vm_state *, g_vm_state, nullptr);

void vm_obj_cell::dec_ref(vm_obj & o, buffer<vm_obj_cell*> & todelete) {
    if (LEAN_VM_IS_PTR(o.m_data)) {
        vm_obj_cell * c = o.steal_ptr();
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

MK_THREAD_LOCAL_GET(small_object_allocator, get_small_allocator, "vm object");

small_object_allocator & get_vm_allocator() {
    return get_small_allocator();
}

vm_composite::vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data):
    vm_obj_cell(k), m_idx(idx),  m_size(sz) {
    vm_obj * fields = get_field_ptr();
    std::uninitialized_copy(data, data + sz, fields);
}

static vm_obj mk_vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data) {
    lean_assert(k == vm_obj_kind::Constructor || k == vm_obj_kind::Closure);
    return vm_obj(new (get_small_allocator().allocate(sizeof(vm_composite) + sz * sizeof(vm_obj))) vm_composite(k, idx, sz, data));
}

void vm_composite::dealloc(buffer<vm_obj_cell*> & todelete) {
    unsigned sz = m_size;
    vm_obj * fields = get_field_ptr();
    for (unsigned i = 0; i < sz; i++) {
        dec_ref(fields[i], todelete);
    }
    this->~vm_composite();
    get_small_allocator().deallocate(sizeof(vm_composite) + sz * sizeof(vm_obj), this);
}

vm_obj mk_vm_constructor(unsigned cidx, unsigned sz, vm_obj const * data) {
    if (g_vm_state && g_vm_state->profiling()) {
        g_vm_state->inc_constructor_allocs();
    }
    return mk_vm_composite(vm_obj_kind::Constructor, cidx, sz, data);
}

vm_obj mk_vm_constructor(unsigned cidx, std::initializer_list<vm_obj const> args) {
    return mk_vm_constructor(cidx, args.size(), args.begin());
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1) {
    return mk_vm_constructor(cidx, 1, &o1);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2) {
    vm_obj args[2] = {o1, o2};
    return mk_vm_constructor(cidx, 2, args);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3) {
    vm_obj args[3] = {o1, o2, o3};
    return mk_vm_constructor(cidx, 3, args);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3, vm_obj const & o4) {
    vm_obj args[4] = {o1, o2, o3, o4};
    return mk_vm_constructor(cidx, 4, args);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3, vm_obj const & o4, vm_obj const & o5) {
    vm_obj args[5] = {o1, o2, o3, o4, o5};
    return mk_vm_constructor(cidx, 5, args);
}

vm_obj update_vm_constructor(vm_obj const & o, unsigned i, vm_obj const & v) {
    lean_vm_check(i < csize(o));
    if (o.raw()->get_rc() == 1) {
        vm_obj * fs = const_cast<vm_obj*>(cfields(o));
        fs[i]       = v;
        return o;
    } else {
        vm_obj r    = mk_vm_constructor(cidx(o), csize(o), cfields(o));
        vm_obj * fs = const_cast<vm_obj*>(cfields(r));
        fs[i]       = v;
        return r;
    }
}

vm_obj update_vm_pair(vm_obj const & o, vm_obj const & v_1, vm_obj const & v_2) {
    lean_vm_check(csize(o) == 2);
    if (o.raw()->get_rc() == 1) {
        vm_obj * fs = const_cast<vm_obj*>(cfields(o));
        fs[0]       = v_1;
        fs[1]       = v_2;
        return o;
    } else {
        return mk_vm_pair(v_1, v_2);
    }
}

vm_obj mk_vm_closure(unsigned fn_idx, unsigned sz, vm_obj const * data) {
    if (g_vm_state && g_vm_state->profiling()) {
        g_vm_state->inc_closure_allocs();
    }
    return mk_vm_composite(vm_obj_kind::Closure, fn_idx, sz, data);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1) {
    return mk_vm_closure(cidx, 1, &o1);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2) {
    vm_obj args[2] = {o1, o2};
    return mk_vm_closure(cidx, 2, args);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3) {
    vm_obj args[3] = {o1, o2, o3};
    return mk_vm_closure(cidx, 3, args);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3, vm_obj const & o4) {
    vm_obj args[4] = {o1, o2, o3, o4};
    return mk_vm_closure(cidx, 4, args);
}

vm_mpz::vm_mpz(mpz const & v):
    vm_obj_cell(vm_obj_kind::MPZ),
    m_value(v) {
    if (g_vm_state && g_vm_state->profiling()) {
        g_vm_state->inc_mpz_allocs();
    }
}

vm_obj mk_vm_simple(unsigned v) {
    return vm_obj(v);
}

vm_obj mk_vm_mpz(mpz const & v) {
    return vm_obj(new (get_small_allocator().allocate(sizeof(vm_mpz))) vm_mpz(v));
}

void vm_mpz::dealloc() {
    this->~vm_mpz();
    get_small_allocator().deallocate(sizeof(vm_mpz), this);
}

/* TODO(Leo, Jared): delete mk_native_closure that takes environment as argument */
vm_obj mk_native_closure(environment const & env, name const & n, std::initializer_list<vm_obj const> args) {
    return mk_native_closure(env, n, args.size(), args.begin());
}

vm_obj mk_native_closure(environment const & /* env */, name const & n, unsigned /* sz */, vm_obj const * /* data */) {
    return get_vm_state().get_constant(n);
}

vm_native_closure::vm_native_closure(vm_cfunction fn, unsigned arity, unsigned num_args, vm_obj const * args):
    vm_obj_cell(vm_obj_kind::NativeClosure), m_fn(fn), m_arity(arity), m_num_args(num_args) {
    /* If the following assertion fails, then it is not necessary to create a closure */
    lean_assert(arity > num_args);
    vm_obj * new_args = get_args_ptr();
    std::uninitialized_copy(args, args + num_args, new_args);
}

void vm_native_closure::dealloc(buffer<vm_obj_cell*> & todelete) {
    vm_obj * args  = get_args_ptr();
    unsigned nargs = m_num_args;
    for (unsigned i = 0; i < nargs; i++) {
        dec_ref(args[i], todelete);
    }
    this->~vm_native_closure();
    get_small_allocator().deallocate(sizeof(vm_native_closure) + nargs * sizeof(vm_obj), this);
}

vm_obj mk_native_closure(vm_cfunction fn, unsigned arity, unsigned num_args, vm_obj const * args) {
    return vm_obj(new (get_small_allocator().allocate(sizeof(vm_native_closure) + num_args * sizeof(vm_obj))) vm_native_closure(fn, arity, num_args, args));
}

vm_obj mk_native_closure(vm_cfunction fn, unsigned arity, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, arity, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_1 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 1, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_2 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 2, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_3 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 3, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_4 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 4, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_5 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 5, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_6 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 6, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_7 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 7, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_8 fn, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), 8, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_N fn, unsigned arity, unsigned num_args, vm_obj const * args) {
    return mk_native_closure(reinterpret_cast<vm_cfunction>(fn), arity, num_args, args);
}

vm_obj mk_native_closure(vm_cfunction_1 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_2 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_3 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_4 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_5 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_6 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_7 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_8 fn, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, args.size(), args.begin());
}

vm_obj mk_native_closure(vm_cfunction_N fn, unsigned arity, std::initializer_list<vm_obj> const & args) {
    return mk_native_closure(fn, arity, args.size(), args.begin());
}

void vm_obj_cell::dealloc() {
    try {
        buffer<vm_obj_cell*> todo;
        todo.push_back(this);
        while (!todo.empty()) {
            vm_obj_cell * it = todo.back();
            todo.pop_back();
            lean_assert(it->get_rc() == 0);
            switch (it->kind()) {
            case vm_obj_kind::Simple:        lean_unreachable();
            case vm_obj_kind::Constructor:   to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::Closure:       to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::MPZ:           to_mpz_core(it)->dealloc(); break;
            case vm_obj_kind::External:      to_external(it)->dealloc(); break;
            case vm_obj_kind::NativeClosure: to_native_closure(it)->dealloc(todo); break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

void display(std::ostream & out, vm_obj const & o) {
    if (is_simple(o)) {
        out << "#" << cidx(o);
    } else if (is_constructor(o)) {
        out << "(#" << cidx(o);
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i));
        }
        out << ")";
    } else if (is_mpz(o)) {
        out << to_mpz(o);
    } else if (is_external(o)) {
        out << "[external]";
    } else if (is_closure(o)) {
        if (auto n = find_vm_name(cfn_idx(o))) {
            out << "(" << *n;
        } else {
            out << "(fn#" << cfn_idx(o);
        }
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i));
        }
        out << ")";
    } else if (is_native_closure(o)) {
        out << "([native_closure]";
        vm_obj const * args = to_native_closure(o)->get_args();
        for (unsigned i = 0; i < to_native_closure(o)->get_num_args(); i++) {
            out << " ";
            display(out, args[i]);
        }
        out << ")";
    } else {
        out << "[unknown]";
    }
}

struct vm_obj_cell_hash {
    unsigned operator()(vm_obj_cell const * o) const { return hash_ptr(o); }
};

struct vm_obj_cell_eq {
    bool operator()(vm_obj_cell const * o1, vm_obj_cell const * o2) const { return o1 == o2; }
};

struct ts_vm_obj::to_ts_vm_obj_fn {
    std::unordered_map<vm_obj_cell *, vm_obj, vm_obj_cell_hash, vm_obj_cell_eq> m_cache;
    std::vector<vm_obj_cell*> & m_objs;
    vm_clone_fn                 m_fn;

    void * alloc_composite(unsigned sz) {
        return new char[sizeof(vm_composite) + sz * sizeof(vm_obj)];
    }

    void * alloc_native_closure(unsigned num_args) {
        return new char[sizeof(vm_native_closure) + num_args * sizeof(vm_obj)];
    }

    vm_obj visit_constructor(vm_obj const & o) {
        buffer<vm_obj> fields;
        for (unsigned i = 0; i < csize(o); i++)
            fields.push_back(visit(cfield(o, i)));
        return vm_obj(new (alloc_composite(fields.size())) vm_composite(vm_obj_kind::Constructor, cidx(o), fields.size(), fields.data()));
    }

    vm_obj visit_closure(vm_obj const & o) {
        buffer<vm_obj> fields;
        for (unsigned i = 0; i < csize(o); i++)
            fields.push_back(visit(cfield(o, i)));
        return vm_obj(new (alloc_composite(fields.size())) vm_composite(vm_obj_kind::Closure, cfn_idx(o), fields.size(), fields.data()));
    }

    vm_obj visit_mpz(vm_obj const & o) {
        return vm_obj(new vm_mpz(to_mpz(o)));
    }

    vm_obj visit_external(vm_obj const & o) {
        return mk_vm_external(to_external(o)->ts_clone(m_fn));
    }

    vm_obj visit_native_closure(vm_obj const & o) {
        vm_native_closure * cell = to_native_closure(o);
        buffer<vm_obj> args;
        unsigned nargs = cell->get_num_args();
        for (unsigned i = 0; i < nargs; i++)
            args.push_back(visit(cell->get_args()[i]));
        return vm_obj(new (alloc_native_closure(nargs)) vm_native_closure(cell->get_fn(), cell->get_arity(),
                                                                          nargs, args.data()));
    }

    vm_obj visit(vm_obj const & o) {
        if (is_simple(o)) return o;
        auto it = m_cache.find(o.raw());
        if (it != m_cache.end())
            return it->second;
        vm_obj r;
        switch (o.kind()) {
        case vm_obj_kind::Simple:        lean_unreachable();
        case vm_obj_kind::Constructor:   r = visit_constructor(o); break;
        case vm_obj_kind::Closure:       r = visit_closure(o); break;
        case vm_obj_kind::MPZ:           r = visit_mpz(o); break;
        case vm_obj_kind::External:      r = visit_external(o); break;
        case vm_obj_kind::NativeClosure: r = visit_native_closure(o); break;
        }
        m_objs.push_back(r.raw());
        m_cache.insert(mk_pair(o.raw(), r));
        return r;
    }

    to_ts_vm_obj_fn(std::vector<vm_obj_cell*> & objs):
        m_objs(objs), m_fn([&](vm_obj const & o) { return visit(o); }) {}

    vm_obj operator()(vm_obj const & o) { return visit(o); }
};

ts_vm_obj::ts_vm_obj(vm_obj const & o) {
    m_data = std::make_shared<data>();
    m_data->m_root = to_ts_vm_obj_fn(m_data->m_objs)(o);
}

ts_vm_obj::data::~data() {
    if (!is_simple(m_root)) steal_ptr(m_root);
    for (vm_obj_cell * cell : m_objs) {
        switch (cell->kind()) {
        case vm_obj_kind::Simple:
            /* We should not use lean_unreachable, since it throws an exception, and
               some compiler complain about code that may throw exceptions in destructors.
            */
            lean_assert(false);
            break;
        case vm_obj_kind::Constructor:
        case vm_obj_kind::Closure:
            static_cast<vm_composite*>(cell)->~vm_composite();
            delete[] reinterpret_cast<char*>(cell);
            break;
        case vm_obj_kind::MPZ:
            delete static_cast<vm_mpz*>(cell);
            break;
        case vm_obj_kind::External:
            delete static_cast<vm_external*>(cell);
            break;
        case vm_obj_kind::NativeClosure:
            static_cast<vm_native_closure*>(cell)->~vm_native_closure();
            delete[] reinterpret_cast<char*>(cell);
            break;
        }
    }
}

struct ts_vm_obj::to_vm_obj_fn {
    std::unordered_map<vm_obj_cell *, vm_obj, vm_obj_cell_hash, vm_obj_cell_eq> m_cache;
    vm_clone_fn m_fn;

    vm_obj visit_constructor(vm_obj const & o) {
        buffer<vm_obj> fields;
        for (unsigned i = 0; i < csize(o); i++)
            fields.push_back(visit(cfield(o, i)));
        return mk_vm_constructor(cidx(o), fields.size(), fields.data());
    }

    vm_obj visit_closure(vm_obj const & o) {
        buffer<vm_obj> fields;
        for (unsigned i = 0; i < csize(o); i++)
            fields.push_back(visit(cfield(o, i)));
        return mk_vm_closure(cfn_idx(o), fields.size(), fields.data());
    }

    vm_obj visit_mpz(vm_obj const & o) {
        return mk_vm_mpz(to_mpz(o));
    }

    vm_obj visit_external(vm_obj const & o) {
        return mk_vm_external(to_external(o)->clone(m_fn));
    }

    vm_obj visit_native_closure(vm_obj const & o) {
        vm_native_closure * cell = to_native_closure(o);
        buffer<vm_obj> args;
        for (unsigned i = 0; i < cell->get_num_args(); i++)
            args.push_back(visit(cell->get_args()[i]));
        return mk_native_closure(cell->get_fn(), cell->get_arity(), args.size(), args.data());
    }

    vm_obj visit(vm_obj const & o) {
        if (is_simple(o)) return o;
        auto it = m_cache.find(o.raw());
        if (it != m_cache.end())
            return it->second;
        vm_obj r;
        switch (o.kind()) {
        case vm_obj_kind::Simple:        lean_unreachable();
        case vm_obj_kind::Constructor:   r = visit_constructor(o); break;
        case vm_obj_kind::Closure:       r = visit_closure(o); break;
        case vm_obj_kind::MPZ:           r = visit_mpz(o); break;
        case vm_obj_kind::External:      r = visit_external(o); break;
        case vm_obj_kind::NativeClosure: r = visit_native_closure(o); break;
        }
        m_cache.insert(mk_pair(o.raw(), r));
        return r;
    }

    vm_obj operator()(vm_obj const & o) { return visit(o); }

    to_vm_obj_fn():m_fn([&](vm_obj const & o) { return visit(o); }) {}
};

vm_obj ts_vm_obj::to_vm_obj() const {
    return to_vm_obj_fn()(m_data->m_root);
}

static void display_fn(std::ostream & out, unsigned fn_idx) {
    if (auto r = find_vm_name(fn_idx))
        out << *r;
    else
        out << fn_idx;
}

static void display_builtin_cases(std::ostream & out, unsigned cases_idx) {
    display_fn(out, cases_idx);
}

void vm_instr::display(std::ostream & out) const {
    switch (m_op) {
    case opcode::Push:          out << "push " << m_idx; break;
    case opcode::Move:          out << "move " << m_idx; break;
    case opcode::Ret:           out << "ret"; break;
    case opcode::Drop:          out << "drop " << m_num; break;
    case opcode::Goto:          out << "goto " << m_pc[0]; break;
    case opcode::SConstructor:  out << "scnstr #" << m_cidx; break;
    case opcode::Constructor:   out << "cnstr #" << m_cidx << " " << m_nfields; break;
    case opcode::Num:           out << "num " << *m_mpz; break;
    case opcode::Unreachable:   out << "unreachable"; break;
    case opcode::Destruct:      out << "destruct"; break;
    case opcode::Cases2:        out << "cases2 " << m_pc[1]; break;
    case opcode::CasesN:
        out << "cases";
        for (unsigned i = 0; i < get_casesn_size(); i++)
            out << " " << get_casesn_pc(i);
        break;
    case opcode::BuiltinCases:
        out << "builtin_cases ";
        display_builtin_cases(out, get_cases_idx());
        out << ",";
        for (unsigned i = 0; i < get_casesn_size(); i++)
            out << " " << get_casesn_pc(i);
        break;
    case opcode::NatCases:      out << "nat_cases " << m_pc[1]; break;
    case opcode::Proj:          out << "proj " << m_idx; break;
    case opcode::Apply:         out << "apply"; break;
    case opcode::InvokeGlobal:
        out << "ginvoke ";
        display_fn(out, m_fn_idx);
        break;
    case opcode::InvokeBuiltin:
        out << "builtin ";
        display_fn(out, m_fn_idx);
        break;
    case opcode::InvokeCFun:
        out << "cfun ";
        display_fn(out, m_fn_idx);
        break;
    case opcode::Closure:
        out << "closure ";
        display_fn(out, m_fn_idx);
        out << " " << m_nargs;
        break;
    case opcode::Expr:
        out << "pexpr " << *m_expr; break;
    case opcode::LocalInfo:
        out << "localinfo " << m_local_info->first << " @ " << m_local_idx; break;
    }
}

unsigned vm_instr::get_num_pcs() const {
    switch (m_op) {
    case opcode::Goto:
        return 1;
    case opcode::Cases2: case opcode::NatCases:
        return 2;
    case opcode::CasesN: case opcode::BuiltinCases:
        return get_casesn_size();
    default:
        return 0;
    }
}

unsigned vm_instr::get_pc(unsigned i) const {
    lean_assert(i < get_num_pcs());
    switch (m_op) {
    case opcode::Goto:
    case opcode::Cases2: case opcode::NatCases:
        return m_pc[i];
    case opcode::CasesN: case opcode::BuiltinCases:
        return get_casesn_pc(i);
    default:
        lean_unreachable();
    }
}

void vm_instr::set_pc(unsigned i, unsigned pc) {
    lean_assert(i < get_num_pcs());
    switch (m_op) {
    case opcode::Goto:
    case opcode::Cases2: case opcode::NatCases:
        m_pc[i] = pc;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        set_casesn_pc(i, pc);
        break;
    default:
        lean_unreachable();
    }
}

vm_instr mk_push_instr(unsigned idx) {
    vm_instr r(opcode::Push);
    r.m_idx = idx;
    return r;
};

vm_instr mk_move_instr(unsigned idx) {
    vm_instr r(opcode::Move);
    r.m_idx = idx;
    return r;
};

vm_instr mk_drop_instr(unsigned n) {
    vm_instr r(opcode::Drop);
    r.m_num = n;
    return r;
}

vm_instr mk_proj_instr(unsigned n) {
    vm_instr r(opcode::Proj);
    r.m_idx = n;
    return r;
}

vm_instr mk_goto_instr(unsigned pc) {
    vm_instr r(opcode::Goto);
    r.m_pc[0] = pc;
    return r;
}

vm_instr mk_sconstructor_instr(unsigned cidx) {
    vm_instr r(opcode::SConstructor);
    r.m_cidx = cidx;
    return r;
}

vm_instr mk_constructor_instr(unsigned cidx, unsigned nfields) {
    vm_instr r(opcode::Constructor);
    r.m_cidx    = cidx;
    r.m_nfields = nfields;
    return r;
}

vm_instr mk_num_instr(mpz const & v) {
    if (v < LEAN_MAX_SMALL_NAT) {
        vm_instr r(opcode::SConstructor);
        r.m_num = v.get_unsigned_int();
        return r;
    } else {
        vm_instr r(opcode::Num);
        r.m_mpz = new mpz(v);
        return r;
    }
}

vm_instr mk_expr_instr(expr const &v) {
    vm_instr r(opcode::Expr);
    r.m_expr = new expr(v);
    return r;
}

vm_instr mk_local_info_instr(unsigned idx, name const & n, optional<expr> const & e) {
    vm_instr r(opcode::LocalInfo);
    r.m_local_idx  = idx;
    r.m_local_info = new vm_local_info(n, e);
    return r;
}

vm_instr mk_ret_instr() { return vm_instr(opcode::Ret); }

vm_instr mk_destruct_instr() { return vm_instr(opcode::Destruct); }

vm_instr mk_unreachable_instr() { return vm_instr(opcode::Unreachable); }

vm_instr mk_apply_instr() { return vm_instr(opcode::Apply); }

vm_instr mk_nat_cases_instr(unsigned pc1, unsigned pc2) {
    vm_instr r(opcode::NatCases);
    r.m_pc[0] = pc1;
    r.m_pc[1] = pc2;
    return r;
}

vm_instr mk_cases2_instr(unsigned pc1, unsigned pc2) {
    vm_instr r(opcode::Cases2);
    r.m_pc[0] = pc1;
    r.m_pc[1] = pc2;
    return r;
}

vm_instr mk_casesn_instr(unsigned num_pc, unsigned const * pcs) {
    lean_assert(num_pc >= 2);
    vm_instr r(opcode::CasesN);
    r.m_cases_idx = 0; /* not really needed, but it avoids a valgrind warning. */
    r.m_npcs = new unsigned[num_pc + 1];
    r.m_npcs[0] = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_builtin_cases_instr(unsigned cases_idx, unsigned num_pc, unsigned const * pcs) {
    vm_instr r(opcode::BuiltinCases);
    r.m_cases_idx = cases_idx;
    r.m_npcs      = new unsigned[num_pc + 1];
    r.m_npcs[0]   = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_invoke_global_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeGlobal);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_invoke_builtin_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeBuiltin);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_invoke_cfun_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeCFun);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_closure_instr(unsigned fn_idx, unsigned n) {
    vm_instr r(opcode::Closure);
    r.m_fn_idx = fn_idx;
    r.m_nargs  = n;
    return r;
}

void vm_instr::release_memory() {
    switch (m_op) {
    case opcode::CasesN:
    case opcode::BuiltinCases:
        delete[] m_npcs;
        break;
    case opcode::Num:
        delete m_mpz;
        break;
    case opcode::Expr:
        delete m_expr;
        break;
    case opcode::LocalInfo:
        delete m_local_info;
        break;
    default:
        break;
    }
}

void vm_instr::copy_args(vm_instr const & i) {
    switch (i.m_op) {
    case opcode::InvokeGlobal: case opcode::InvokeBuiltin: case opcode::InvokeCFun:
        m_fn_idx = i.m_fn_idx;
        break;
    case opcode::Closure:
        m_fn_idx = i.m_fn_idx;
        m_nargs  = i.m_nargs;
        break;
    case opcode::Push: case opcode::Move: case opcode::Proj:
        m_idx  = i.m_idx;
        break;
    case opcode::Drop:
        m_num = i.m_num;
        break;
    case opcode::Goto:
        m_pc[0] = i.m_pc[0];
        break;
    case opcode::Cases2: case opcode::NatCases:
        m_pc[0] = i.m_pc[0];
        m_pc[1] = i.m_pc[1];
        break;
    case opcode::CasesN:
    case opcode::BuiltinCases:
        m_npcs = new unsigned[i.m_npcs[0] + 1];
        for (unsigned j = 0; j < i.m_npcs[0] + 1; j++)
            m_npcs[j] = i.m_npcs[j];
        m_cases_idx = i.m_cases_idx;
        break;
    case opcode::SConstructor:
        m_cidx = i.m_cidx;
        break;
    case opcode::Constructor:
        m_cidx    = i.m_cidx;
        m_nfields = i.m_nfields;
        break;
    case opcode::Num:
        m_mpz = new mpz(*i.m_mpz);
        break;
    case opcode::Expr:
        m_expr = new expr(*i.m_expr);
        break;
    case opcode::LocalInfo:
        m_local_idx  = i.m_local_idx;
        m_local_info = new vm_local_info(*i.m_local_info);
        break;
    case opcode::Ret:         case opcode::Destruct:
    case opcode::Unreachable: case opcode::Apply:
        break;
    }
}

vm_instr::vm_instr(vm_instr const & i):
    m_op(i.m_op) {
    copy_args(i);
}

vm_instr::vm_instr(vm_instr && i):
    m_op(i.m_op) {
    switch (m_op) {
    case opcode::Num:
        m_mpz    = i.m_mpz;
        i.m_mpz  = nullptr;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        m_npcs      = i.m_npcs;
        m_cases_idx = i.m_cases_idx;
        i.m_npcs    = nullptr;
        break;
    default:
        copy_args(i);
        break;
    }
}

vm_instr::~vm_instr() {
    release_memory();
}

vm_instr & vm_instr::operator=(vm_instr const & s) {
    release_memory();
    m_op = s.m_op;
    copy_args(s);
    return *this;
}

vm_instr & vm_instr::operator=(vm_instr && s) {
    release_memory();
    m_op = s.m_op;
    switch (m_op) {
    case opcode::Num:
        m_mpz    = s.m_mpz;
        s.m_mpz  = nullptr;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        m_cases_idx = s.m_cases_idx;
        m_npcs      = s.m_npcs;
        s.m_npcs    = nullptr;
        break;
    default:
        copy_args(s);
        break;
    }
    return *this;
}

void vm_instr::serialize(serializer & s, std::function<name(unsigned)> const & idx2name) const {
    s << static_cast<char>(m_op);
    switch (m_op) {
    case opcode::InvokeGlobal: case opcode::InvokeBuiltin: case opcode::InvokeCFun:
        s << idx2name(m_fn_idx);
        break;
    case opcode::Closure:
        s << idx2name(m_fn_idx) << m_nargs;
        break;
    case opcode::Push: case opcode::Move: case opcode::Proj:
        s << m_idx;
        break;
    case opcode::Drop:
        s << m_num;
        break;
    case opcode::Goto:
        s << m_pc[0];
        break;
    case opcode::Cases2: case opcode::NatCases:
        s << m_pc[0];
        s << m_pc[1];
        break;
    case opcode::BuiltinCases:
        s << idx2name(m_cases_idx);
        /* fall-thru */
    case opcode::CasesN:
        s << m_npcs[0];
        for (unsigned j = 1; j < m_npcs[0] + 1; j++)
            s << m_npcs[j];
        break;
    case opcode::SConstructor:
        s << m_cidx;
        break;
    case opcode::Constructor:
        s << m_cidx << m_nfields;
        break;
    case opcode::Num:
        s << *m_mpz;
        break;
    case opcode::Expr:
        s << *m_expr;
        break;
    case opcode::LocalInfo:
        s << m_local_idx << m_local_info->first << m_local_info->second;
        break;
    case opcode::Ret:         case opcode::Destruct:
    case opcode::Unreachable: case opcode::Apply:
        break;
    }
}

static unsigned read_fn_idx(deserializer & d) {
    name n;
    d >> n;
    return get_vm_index(n);
}

static void read_cases_pcs(deserializer & d, buffer<unsigned> & pcs) {
    unsigned n = d.read_unsigned();
    for (unsigned j = 0; j < n; j++)
        pcs.push_back(d.read_unsigned());
}

static vm_instr read_vm_instr(deserializer & d) {
    opcode op = static_cast<opcode>(d.read_char());
    unsigned pc, idx;
    switch (op) {
    case opcode::InvokeGlobal:
        return mk_invoke_global_instr(read_fn_idx(d));
    case opcode::InvokeBuiltin:
        return mk_invoke_builtin_instr(read_fn_idx(d));
    case opcode::InvokeCFun:
        return mk_invoke_cfun_instr(read_fn_idx(d));
    case opcode::Closure:
        idx = read_fn_idx(d);
        return mk_closure_instr(idx, d.read_unsigned());
    case opcode::Push:
        return mk_push_instr(d.read_unsigned());
    case opcode::Move:
        return mk_move_instr(d.read_unsigned());
    case opcode::Proj:
        return mk_proj_instr(d.read_unsigned());
    case opcode::Drop:
        return mk_drop_instr(d.read_unsigned());
    case opcode::Goto:
        return mk_goto_instr(d.read_unsigned());
    case opcode::Cases2:
        pc = d.read_unsigned();
        return mk_cases2_instr(pc, d.read_unsigned());
    case opcode::NatCases:
        pc = d.read_unsigned();
        return mk_nat_cases_instr(pc, d.read_unsigned());
    case opcode::CasesN: {
        buffer<unsigned> pcs;
        read_cases_pcs(d, pcs);
        return mk_casesn_instr(pcs.size(), pcs.data());
    }
    case opcode::BuiltinCases: {
        idx = get_vm_index(read_name(d));
        buffer<unsigned> pcs;
        read_cases_pcs(d, pcs);
        return mk_builtin_cases_instr(idx, pcs.size(), pcs.data());
    }
    case opcode::SConstructor:
        return mk_sconstructor_instr(d.read_unsigned());
    case opcode::Constructor:
        idx = d.read_unsigned();
        return mk_constructor_instr(idx, d.read_unsigned());
    case opcode::Num:
        return mk_num_instr(read_mpz(d));
    case opcode::Expr:
        return mk_expr_instr(read_expr(d));
    case opcode::LocalInfo: {
        unsigned idx = d.read_unsigned();
        name n; optional<expr> t;
        d >> n >> t;
        return mk_local_info_instr(idx, n, t);
    }
    case opcode::Ret:
        return mk_ret_instr();
    case opcode::Destruct:
        return mk_destruct_instr();
    case opcode::Unreachable:
        return mk_unreachable_instr();
    case opcode::Apply:
        return mk_apply_instr();
    }
    lean_unreachable();
}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_function fn):
    m_rc(0), m_kind(vm_decl_kind::Builtin), m_name(n), m_idx(idx), m_arity(arity), m_fn(fn) {}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_cfunction fn):
    m_rc(0), m_kind(vm_decl_kind::CFun), m_name(n), m_idx(idx), m_arity(arity), m_cfn(fn) {}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, unsigned code_sz, vm_instr const * code,
                           list<vm_local_info> const & args_info, optional<pos_info> const & pos,
                           optional<std::string> const & olean):
    m_rc(0), m_kind(vm_decl_kind::Bytecode), m_name(n), m_idx(idx), m_arity(arity),
    m_args_info(args_info), m_pos(pos), m_olean(olean),
    m_code_size(code_sz) {
    m_code = new vm_instr[code_sz];
    for (unsigned i = 0; i < code_sz; i++)
        m_code[i] = code[i];
}

vm_decl_cell::~vm_decl_cell() {
    if (m_kind == vm_decl_kind::Bytecode)
        delete[] m_code;
}

void vm_decl_cell::dealloc() {
    delete this;
}

/** \brief VM builtin functions */
static name_map<std::tuple<unsigned, char const *, vm_function>> * g_vm_builtins = nullptr;
static name_map<std::tuple<unsigned, char const *, vm_cfunction>> * g_vm_cbuiltins = nullptr;
static name_map<std::tuple<char const *, vm_cases_function>> * g_vm_cases_builtins = nullptr;
static bool g_may_update_vm_builtins = true;

void declare_vm_builtin(name const & n, char const * i, unsigned arity, vm_function fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_builtins->insert(n, std::make_tuple(arity, i, fn));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_0 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(0, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_1 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(1, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_2 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(2, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_3 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(3, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_4 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(4, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_5 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(5, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_6 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(6, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_7 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(7, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_8 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(8, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, unsigned arity, vm_cfunction_N fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(arity, i, reinterpret_cast<vm_cfunction>(fn)));
}

bool is_vm_builtin_function(name const & fn) {
    return g_vm_builtins->contains(fn) || g_vm_cbuiltins->contains(fn) || g_vm_cases_builtins->contains(fn);
}

void declare_vm_cases_builtin(name const & n, char const * i, vm_cases_function fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cases_builtins->insert(n, std::make_tuple(i, fn));
}

/** \brief VM function/constant declarations are stored in an environment extension. */
struct vm_decls : public environment_extension {
    unsigned_map<vm_decl>           m_decls;
    unsigned_map<vm_cases_function> m_cases;

    name                            m_monitor;

    vm_decls() {
        g_vm_cases_builtins->for_each([&](name const & n, std::tuple<char const *, vm_cases_function> const & p) {
                unsigned idx = get_vm_index(n);
                m_cases.insert(idx, std::get<1>(p));
            });
        g_vm_builtins->for_each([&](name const & n, std::tuple<unsigned, char const *, vm_function> const & p) {
                add_core(vm_decl(n, get_vm_index(n), std::get<0>(p), std::get<2>(p)));
            });
        g_vm_cbuiltins->for_each([&](name const & n, std::tuple<unsigned, char const *, vm_cfunction> const & p) {
                add_core(vm_decl(n, get_vm_index(n), std::get<0>(p), std::get<2>(p)));
            });
    }

    void add_core(vm_decl const & d) {
        if (m_decls.contains(d.get_idx()))
            throw exception(sstream() << "VM already contains code for '" << d.get_name() << "'");
        m_decls.insert(d.get_idx(), d);
    }

    void add_native(name const & n, unsigned arity, vm_cfunction fn) {
        auto idx = get_vm_index(n);
        DEBUG_CODE(if (auto decl = m_decls.find(idx)) lean_assert(decl->get_arity() == arity);)
        m_decls.insert(idx, vm_decl(n, idx, arity, fn));
    }

    unsigned reserve(name const & n, unsigned arity) {
        unsigned idx = get_vm_index(n);
        if (m_decls.contains(idx))
            throw exception(sstream() << "VM already contains code for '" << n << "'");
        m_decls.insert(idx, vm_decl(n, idx, arity, 0, nullptr, list<vm_local_info>(), optional<pos_info>()));
        return idx;
    }

    void update(vm_decl const & new_decl) {
        lean_assert(new_decl.get_idx() == get_vm_index(new_decl.get_name()));
        lean_assert(m_decls.contains(new_decl.get_idx()));
        m_decls.insert(new_decl.get_idx(), new_decl);
    }
};

struct vm_decls_reg {
    std::shared_ptr<vm_decls> m_init_decls;
    unsigned                  m_ext_id;
    vm_decls_reg() {
        m_init_decls = std::make_shared<vm_decls>();
        m_ext_id     = environment::register_extension(m_init_decls);
    }
};

static vm_decls_reg * g_ext = nullptr;
static vm_decls const & get_extension(environment const & env) {
    return static_cast<vm_decls const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, vm_decls const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<vm_decls>(ext));
}

static environment add_native(environment const & env, name const & n, unsigned arity, vm_cfunction fn) {
    auto ext = get_extension(env);
    ext.add_native(n, arity, fn);
    return update(env, ext);
}

environment add_native(environment const & env, name const & n, vm_cfunction_0 fn) {
    return add_native(env, n, 0, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_1 fn) {
    return add_native(env, n, 1, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_2 fn) {
    return add_native(env, n, 2, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_3 fn) {
    return add_native(env, n, 3, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_4 fn) {
    return add_native(env, n, 4, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_5 fn) {
    return add_native(env, n, 5, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_6 fn) {
    return add_native(env, n, 6, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_7 fn) {
    return add_native(env, n, 7, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_8 fn) {
    return add_native(env, n, 8, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, unsigned arity, vm_cfunction_N fn) {
    return add_native(env, n, arity, reinterpret_cast<vm_cfunction>(fn));
}

bool is_vm_function(environment const & env, name const & fn) {
    auto const & ext = get_extension(env);
    return ext.m_decls.contains(get_vm_index(fn)) || g_vm_builtins->contains(fn);
}

optional<unsigned> get_vm_constant_idx(environment const & env, name const & n) {
    auto const & ext = get_extension(env);
    auto idx = get_vm_index(n);
    if (ext.m_decls.contains(idx))
        return optional<unsigned>(idx);
    else
        return optional<unsigned>();
}

optional<unsigned> get_vm_builtin_idx(name const & n) {
    lean_assert(g_ext);
    auto idx = get_vm_index(n);
    if (g_ext->m_init_decls->m_decls.contains(idx))
        return optional<unsigned>(idx);
    else
        return optional<unsigned>();
}

struct vm_reserve_modification : public modification {
    LEAN_MODIFICATION("VMR")

    name     m_fn;
    unsigned m_arity;

    vm_reserve_modification(name const & fn, unsigned arity): m_fn(fn), m_arity(arity) {}

    void perform(environment & env) const override {
        vm_decls ext = get_extension(env);
        ext.reserve(m_fn, m_arity);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_fn << m_arity;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name fn; unsigned arity;
        d >> fn >> arity;
        return std::make_shared<vm_reserve_modification>(fn, arity);
    }
};

struct vm_code_modification : public modification {
    LEAN_MODIFICATION("VMC")

    vm_decl m_decl;

    vm_code_modification(vm_decl const & decl) : m_decl(decl) {}
    vm_code_modification() {}

    void perform(environment & env) const override {
        vm_decls ext = get_extension(env);
        ext.update(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        unsigned code_sz = m_decl.get_code_size();
        s << m_decl.get_name() << m_decl.get_arity() << code_sz << m_decl.get_pos_info();
        write_list(s, m_decl.get_args_info());
        auto c = m_decl.get_code();
        for (unsigned i = 0; i < code_sz; i++)
            c[i].serialize(s, get_vm_name);
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name fn; unsigned arity; unsigned code_sz; optional<pos_info> pos;
        d >> fn >> arity >> code_sz >> pos;
        auto args_info = read_list<vm_local_info>(d);
        buffer<vm_instr> code;
        for (unsigned i = 0; i < code_sz; i++)
            code.emplace_back(read_vm_instr(d));
        optional<std::string> file_name; // TODO(gabriel)
        return std::make_shared<vm_code_modification>(
                vm_decl(fn, get_vm_index(fn), arity, code_sz, code.data(), args_info, pos, file_name));
    }
};

struct vm_monitor_modification : public modification {
    LEAN_MODIFICATION("VMMonitor")

    name m_monitor;

    vm_monitor_modification() {}
    vm_monitor_modification(name const & n) : m_monitor(n) {}

    void perform(environment & env) const override {
        vm_decls ext = get_extension(env);
        ext.m_monitor = m_monitor;
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_monitor;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto m = std::make_shared<vm_monitor_modification>();
        d >> m->m_monitor;
        return m;
    }
};

environment reserve_vm_index(environment const & env, name const & fn, unsigned arity) {
    return module::add_and_perform(env, std::make_shared<vm_reserve_modification>(fn, arity));
}

unsigned get_num_nested_lambdas(expr const & e) {
    unsigned r = 0;
    expr it = e;
    while (is_lambda(it)) {
        r++;
        it = binding_body(it);
    }
    return r;
}

environment reserve_vm_index(environment const & env, name const & fn, expr const & e) {
    return reserve_vm_index(env, fn, get_num_nested_lambdas(e));
}

environment update_vm_code(environment const & env, name const & fn, unsigned code_sz, vm_instr const * code,
                           list<vm_local_info> const & args_info, optional<pos_info> const & pos) {
    vm_decl decl(fn, get_vm_index(fn), get_vm_decl(env, fn)->get_arity(), code_sz, code, args_info, pos);
    return module::add_and_perform(env, std::make_shared<vm_code_modification>(decl));
}

environment add_vm_code(environment const & env, name const & fn, expr const & e, unsigned code_sz, vm_instr const * code,
                        list<vm_local_info> const & args_info, optional<pos_info> const & pos) {
    environment new_env = reserve_vm_index(env, fn, e);
    return update_vm_code(new_env, fn, code_sz, code, args_info, pos);
}

environment add_vm_code(environment const & env, name const & fn, unsigned arity, unsigned code_sz, vm_instr const * code,
                        list<vm_local_info> const & args_info, optional<pos_info> const & pos) {
    environment new_env = reserve_vm_index(env, fn, arity);
    return update_vm_code(new_env, fn, code_sz, code, args_info, pos);
}

optional<vm_decl> get_vm_decl(environment const & env, name const & n) {
    vm_decls const & ext = get_extension(env);
    if (auto decl = ext.m_decls.find(get_vm_index(n)))
        return optional<vm_decl>(*decl);
    else
        return optional<vm_decl>();
}

optional<unsigned> get_vm_builtin_cases_idx(environment const & env, name const & n) {
    vm_decls const & ext = get_extension(env);
    auto idx = get_vm_index(n);
    if (ext.m_cases.contains(idx))
        return optional<unsigned>(idx);
    else
        return optional<unsigned>();
}

constexpr unsigned g_null_fn_idx = -1;

static name * g_debugger = nullptr;

bool get_debugger(options const & opts) {
    return opts.get_bool(*g_debugger, false);
}

static bool has_monitor(environment const & env) {
    return !get_extension(env).m_monitor.is_anonymous();
}

vm_state::vm_state(environment const & env, options const & opts):
    m_env(env),
    m_options(opts),
    m_decl_map(get_extension(m_env).m_decls),
    m_decl_vector(get_vm_index_bound()),
    m_builtin_cases_map(get_extension(m_env).m_cases),
    m_builtin_cases_vector(get_vm_index_bound()),
    m_code(nullptr),
    m_fn_idx(g_null_fn_idx),
    m_bp(0) {
    if (get_debugger(opts) && has_monitor(env)) {
        debugger_init();
    }
}

vm_state::~vm_state() {
}

vm_decl const & vm_state::get_decl(unsigned idx) const {
    lean_assert(idx < m_decl_vector.size());
    vm_decl const & d = m_decl_vector[idx];
    if (d) return d;
    if (auto d_ = m_decl_map.find(idx)) {
        const_cast<vm_state *>(this)->m_decl_vector[idx] = *d_;
    } else {
        lean_unreachable();
    }
    return m_decl_vector[idx];
}

vm_cases_function const & vm_state::get_builtin_cases(unsigned idx) const {
    lean_assert(idx < m_builtin_cases_vector.size());
    vm_cases_function const & fn = m_builtin_cases_vector[idx];
    if (fn != nullptr) return fn;
    if (auto fn_ = m_builtin_cases_map.find(idx)) {
        const_cast<vm_state *>(this)->m_builtin_cases_vector[idx] = *fn_;
    } else {
        lean_unreachable();
    }
    return m_builtin_cases_vector[idx];
}


struct vm_state::debugger_state {
    vm_state m_vm;
    vm_obj   m_state;
    vm_obj   m_step_fn;
    debugger_state(environment const & env):
        m_vm(env, options()) {
        auto const & ext = get_extension(env);
        vm_obj o  = m_vm.invoke(ext.m_monitor, {});
        m_state   = cfield(o, 0);
        m_step_fn = cfield(o, 1);
    }
};

void vm_state::debugger_init() {
    m_debugging          = true;
    m_debugger_state_ptr.reset(new debugger_state(m_env));
}

scope_vm_state::scope_vm_state(vm_state & s):
    m_prev(g_vm_state) {
    g_vm_state = &s;
}

scope_vm_state::~scope_vm_state() {
    g_vm_state = m_prev;
}

/* Reference to the VM that is currently being debugged. */
LEAN_THREAD_VALUE(vm_state *, g_vm_state_debugged, nullptr);

vm_state & get_vm_state_being_debugged() {
    lean_assert(g_vm_state_debugged);
    return *g_vm_state_debugged;
}

void vm_state::debugger_step() {
    flet<vm_state*> set1(g_vm_state_debugged, this);
    auto & vm_dbg  = m_debugger_state_ptr->m_vm;
    flet<vm_state*> set2(g_vm_state, &vm_dbg);
    vm_obj r       =
        vm_dbg.invoke(m_debugger_state_ptr->m_step_fn,
                      m_debugger_state_ptr->m_state,
                      mk_vm_unit());
    if (!is_none(r))
        m_debugger_state_ptr->m_state = get_some_value(r);
}

void vm_state::update_env(environment const & env) {
    lean_assert(env.is_descendant(env));
    m_env         = env;
    auto ext      = get_extension(env);
    m_decl_map    = ext.m_decls;
    m_decl_vector.resize(get_vm_index_bound());
    m_was_updated = true;
    lean_assert(is_eqp(m_builtin_cases_map, ext.m_cases));
}

void vm_state::push_fields(vm_obj const & obj) {
    if (is_constructor(obj)) {
        unsigned nflds = csize(obj);
        vm_obj const * flds = cfields(obj);
        for (unsigned i = 0; i < nflds; i++, flds++) {
            m_stack.push_back(*flds);
        }
    }
}

void vm_state::shrink_stack_info() {
    if (m_stack.empty()) {
        m_stack_info.clear();
    } else {
        /* The information on top of the m_stack_info has been invalidated.
           The information is invalidated by a swap or push_back operation
           at m_stack. */
        m_stack_info.resize(m_stack.size() - 1);
    }
}

void vm_state::stack_pop_back() {
    m_stack.pop_back();
    if (m_debugging)
        m_stack_info.resize(m_stack.size());
}

void vm_state::invoke_builtin(vm_decl const & d) {
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        push_frame_core(0, 0, d.get_idx());
    }
    unsigned saved_bp = m_bp;
    unsigned sz = m_stack.size();
    m_bp = sz;
    d.get_fn()(*this);
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        m_call_stack.pop_back();
    }
    lean_assert(m_stack.size() == sz + 1);
    m_bp = saved_bp;
    sz = m_stack.size();
    swap(m_stack[sz - d.get_arity() - 1], m_stack[sz - 1]);
    m_stack.resize(sz - d.get_arity());
    if (m_debugging) shrink_stack_info();
    m_pc++;
}

void vm_state::invoke_fn(vm_cfunction fn, unsigned arity) {
    flet<vm_state *> Set(g_vm_state, this);
    auto & S       = m_stack;
    unsigned sz    = S.size();
    lean_vm_check(arity <= sz);
    vm_obj r;
    /* Important The stack m_stack may be resized during the execution of the function d.get_cfn().
       Thus, to make sure the arguments are not garbage collected, we copy them into local variables a1 ... an.
       The copy operation will bump the reference counter. */
    switch (arity) {
    case 0:
        r = reinterpret_cast<vm_cfunction_0>(fn)();
        break;
    case 1: {
        vm_obj a1 = S[sz-1];
        m_stack.resize(sz - 1);
        r = reinterpret_cast<vm_cfunction_1>(fn)(a1);
        break;
    }
    case 2: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2];
        m_stack.resize(sz - 2);
        r = reinterpret_cast<vm_cfunction_2>(fn)(a1, a2);
        break;
    }
    case 3: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3];
        m_stack.resize(sz - 3);
        r = reinterpret_cast<vm_cfunction_3>(fn)(a1, a2, a3);
        break;
    }
    case 4: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4];
        m_stack.resize(sz - 4);
        r = reinterpret_cast<vm_cfunction_4>(fn)(a1, a2, a3, a4);
        break;
    }
    case 5: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5];
        m_stack.resize(sz - 5);
        r = reinterpret_cast<vm_cfunction_5>(fn)(a1, a2, a3, a4, a5);
        break;
    }
    case 6: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        m_stack.resize(sz - 6);
        r = reinterpret_cast<vm_cfunction_6>(fn)(a1, a2, a3, a4, a5, a6);
        break;
    }
    case 7: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        vm_obj a7 = S[sz - 7];
        m_stack.resize(sz - 7);
        r = reinterpret_cast<vm_cfunction_7>(fn)(a1, a2, a3, a4, a5, a6, a7);
        break;
    }
    case 8: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        vm_obj a7 = S[sz - 7], a8 = S[sz - 8];
        m_stack.resize(sz - 8);
        r = reinterpret_cast<vm_cfunction_8>(fn)(a1, a2, a3, a4, a5, a6, a7, a8);
        break;
    }
    default: {
        buffer<vm_obj> args;
        unsigned i = sz;
        while (i > sz - arity) {
            --i;
            args.push_back(m_stack[i]);
        }
        lean_assert(args.size() == arity);
        m_stack.resize(sz - arity);
        r = reinterpret_cast<vm_cfunction_N>(fn)(args.size(), args.data());
        break;
    }}
    m_stack.push_back(r);
    if (m_debugging) shrink_stack_info();
    m_pc++;
}

inline vm_cfunction_1 to_fn1(vm_decl const & d) { return reinterpret_cast<vm_cfunction_1>(d.get_cfn()); }
inline vm_cfunction_2 to_fn2(vm_decl const & d) { return reinterpret_cast<vm_cfunction_2>(d.get_cfn()); }
inline vm_cfunction_3 to_fn3(vm_decl const & d) { return reinterpret_cast<vm_cfunction_3>(d.get_cfn()); }
inline vm_cfunction_4 to_fn4(vm_decl const & d) { return reinterpret_cast<vm_cfunction_4>(d.get_cfn()); }
inline vm_cfunction_5 to_fn5(vm_decl const & d) { return reinterpret_cast<vm_cfunction_5>(d.get_cfn()); }
inline vm_cfunction_6 to_fn6(vm_decl const & d) { return reinterpret_cast<vm_cfunction_6>(d.get_cfn()); }
inline vm_cfunction_7 to_fn7(vm_decl const & d) { return reinterpret_cast<vm_cfunction_7>(d.get_cfn()); }
inline vm_cfunction_8 to_fn8(vm_decl const & d) { return reinterpret_cast<vm_cfunction_8>(d.get_cfn()); }
inline vm_cfunction_N to_fnN(vm_decl const & d) { return reinterpret_cast<vm_cfunction_N>(d.get_cfn()); }

vm_obj vm_state::invoke_closure(vm_obj const & fn, unsigned DEBUG_CODE(nargs)) {
    unsigned saved_pc = m_pc;
    unsigned fn_idx   = cfn_idx(fn);
    vm_decl d         = get_decl(fn_idx);
    unsigned csz      = csize(fn);
    std::copy(cfields(fn), cfields(fn) + csz, std::back_inserter(m_stack));
    lean_assert(nargs + csz == d.get_arity());
    switch (d.kind()) {
    case vm_decl_kind::Bytecode:
        invoke_global(d);
        run();
        break;
    case vm_decl_kind::Builtin:
        invoke_builtin(d);
        break;
    case vm_decl_kind::CFun:
        invoke_cfun(d);
        break;
    }
    m_pc     = saved_pc;
    vm_obj r = m_stack.back();
    stack_pop_back();
    return r;
}

static void to_cbuffer(vm_obj const & fn, buffer<vm_obj> & args) {
    vm_obj const * begin = cfields(fn);
    vm_obj const * end   = begin + csize(fn);
    vm_obj const * it    = end;
    while (it != begin) {
        --it;
        args.push_back(*it);
    }
}

vm_obj vm_state::invoke(unsigned fn_idx, unsigned nargs, vm_obj const * as) {
    vm_decl d = get_decl(fn_idx);
    lean_assert(d.get_arity() <= nargs);
    std::copy(as, as + nargs, std::back_inserter(m_stack));
    invoke_fn(fn_idx);
    if (d.get_arity() < nargs)
        apply(nargs - d.get_arity());
    vm_obj r = m_stack.back();
    stack_pop_back();
    return r;
}

vm_obj vm_state::invoke(name const & fn, unsigned nargs, vm_obj const * as) {
    auto idx = get_vm_index(fn);
    if (m_decl_map.contains(idx)) {
        return invoke(idx, nargs, as);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 1;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: lean_unreachable();
            case 1: return to_fn1(d)(a1);
            case 2: return to_fn2(d)(cfield(fn, 0), a1);
            case 3: return to_fn3(d)(cfield(fn, 1), cfield(fn, 0), a1);
            case 4: return to_fn4(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 5: return to_fn5(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 6: return to_fn6(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 7: return to_fn7(d)(cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 8: return to_fn8(d)(cfield(fn, 6), cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a1);
            return invoke_closure(fn, 1);
        }
    } else {
        lean_unreachable();
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 2;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: lean_unreachable();
            case 2: return to_fn2(d)(a1, a2);
            case 3: return to_fn3(d)(cfield(fn, 0), a1, a2);
            case 4: return to_fn4(d)(cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 5: return to_fn5(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 6: return to_fn6(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 7: return to_fn7(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 8: return to_fn8(d)(cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 2);
        }
    } else {
        lean_assert(nargs > d.get_arity());
        return ::lean::invoke(invoke(fn, a1), a2);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 3;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: lean_unreachable();
            case 3: return to_fn3(d)(a1, a2, a3);
            case 4: return to_fn4(d)(cfield(fn, 0), a1, a2, a3);
            case 5: return to_fn5(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 6: return to_fn6(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 7: return to_fn7(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 8: return to_fn8(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 3);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2), a3);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 4;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: lean_unreachable();
            case 4: return to_fn4(d)(a1, a2, a3, a4);
            case 5: return to_fn5(d)(cfield(fn, 0), a1, a2, a3, a4);
            case 6: return to_fn6(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            case 7: return to_fn7(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            case 8: return to_fn8(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 4);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2, a3), a4);
    } else if (nargs == d.get_arity() + 2) {
        return ::lean::invoke(invoke(fn, a1, a2), a3, a4);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3, a4);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 5;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: lean_unreachable();
            case 5: return to_fn5(d)(a1, a2, a3, a4, a5);
            case 6: return to_fn6(d)(cfield(fn, 0), a1, a2, a3, a4, a5);
            case 7: return to_fn7(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5);
            case 8: return to_fn8(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 5);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4), a5);
    } else if (nargs == d.get_arity() + 2) {
        return ::lean::invoke(invoke(fn, a1, a2, a3), a4, a5);
    } else if (nargs == d.get_arity() + 3) {
        return ::lean::invoke(invoke(fn, a1, a2), a3, a4, a5);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3, a4, a5);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 6;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: lean_unreachable();
            case 6: return to_fn6(d)(a1, a2, a3, a4, a5, a6);
            case 7: return to_fn7(d)(cfield(fn, 0), a1, a2, a3, a4, a5, a6);
            case 8: return to_fn8(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5, a6);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 6);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5), a6);
    } else if (nargs == d.get_arity() + 2) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4), a5, a6);
    } else if (nargs == d.get_arity() + 3) {
        return ::lean::invoke(invoke(fn, a1, a2, a3), a4, a5, a6);
    } else if (nargs == d.get_arity() + 4) {
        return ::lean::invoke(invoke(fn, a1, a2), a3, a4, a5, a6);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3, a4, a5, a6);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6, vm_obj const & a7) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 7;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a7);
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: case 6: lean_unreachable();
            case 7: return to_fn7(d)(a1, a2, a3, a4, a5, a6, a7);
            case 8: return to_fn8(d)(cfield(fn, 0), a1, a2, a3, a4, a5, a6, a7);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                args.push_back(a7);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a7);
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 7);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5, a6), a7);
    } else if (nargs == d.get_arity() + 2) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5), a6, a7);
    } else if (nargs == d.get_arity() + 3) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4), a5, a6, a7);
    } else if (nargs == d.get_arity() + 4) {
        return ::lean::invoke(invoke(fn, a1, a2, a3), a4, a5, a6, a7);
    } else if (nargs == d.get_arity() + 5) {
        return ::lean::invoke(invoke(fn, a1, a2), a3, a4, a5, a6, a7);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3, a4, a5, a6, a7);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 8;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a8);
        args.push_back(a7);
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7: lean_unreachable();
            case 8: return to_fn8(d)(a1, a2, a3, a4, a5, a6, a7, a8);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                args.push_back(a7);
                args.push_back(a8);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a8);
            m_stack.push_back(a7);
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 8);
        }
    } else if (nargs == d.get_arity() + 1) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5, a6, a7), a8);
    } else if (nargs == d.get_arity() + 2) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5, a6), a7, a8);
    } else if (nargs == d.get_arity() + 3) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4, a5), a6, a7, a8);
    } else if (nargs == d.get_arity() + 4) {
        return ::lean::invoke(invoke(fn, a1, a2, a3, a4), a5, a6, a7, a8);
    } else if (nargs == d.get_arity() + 5) {
        return ::lean::invoke(invoke(fn, a1, a2, a3), a4, a5, a6, a7, a8);
    } else if (nargs == d.get_arity() + 6) {
        return ::lean::invoke(invoke(fn, a1, a2), a3, a4, a5, a6, a7, a8);
    } else {
        return ::lean::invoke(invoke(fn, a1), a2, a3, a4, a5, a6, a7, a8);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    if (nargs <= 8) {
        switch (nargs) {
        case 1: return invoke(fn, args[0]);
        case 2: return invoke(fn, args[0], args[1]);
        case 3: return invoke(fn, args[0], args[1], args[2]);
        case 4: return invoke(fn, args[0], args[1], args[2], args[3]);
        case 5: return invoke(fn, args[0], args[1], args[2], args[3], args[4]);
        case 6: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        case 8: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
        default: lean_unreachable();
        }
    }
    unsigned fn_idx    = cfn_idx(fn);
    vm_decl d          = get_decl(fn_idx);
    unsigned new_nargs = csize(fn) + nargs;
    if (new_nargs < d.get_arity()) {
        buffer<vm_obj> new_args;
        unsigned i = nargs;
        while (i > 0) { --i; new_args.push_back(args[i]); }
        new_args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, new_args.size(), new_args.data());
    } else if (new_nargs == d.get_arity()) {
        if (d.is_cfun()) {
            if (csize(fn) == 0) {
                return to_fnN(d)(nargs, args);
            } else {
                buffer<vm_obj> new_args;
                to_cbuffer(fn, new_args);
                new_args.append(nargs, args);
                return to_fnN(d)(nargs, args);
            }
        } else {
            unsigned i = nargs;
            while (i > 0) { --i; m_stack.push_back(args[i]); }
            return invoke_closure(fn, nargs);
        }
    } else {
        lean_assert(new_nargs > d.get_arity());
        buffer<vm_obj> new_args;
        buffer<vm_obj> rest_args;
        /* copy arity - csize(fn) arguments to new_args, and the rest to rest_args */
        lean_assert(csize(fn) < d.get_arity());
        unsigned n = d.get_arity() - csize(fn);
        lean_assert(n > 1);
        lean_assert(n < nargs);
        new_args.append(n, args);
        rest_args.append(nargs - n, args + n);
        return ::lean::invoke(invoke(fn, new_args.size(), new_args.data()), rest_args.size(), rest_args.data());
    }
}

optional<vm_obj> vm_state::try_invoke_catch(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    auto     code           = m_code;
    unsigned fn_idx         = m_fn_idx;
    unsigned pc             = m_pc;
    unsigned bp             = m_bp;
    unsigned next_frame_idx = m_next_frame_idx;
    unsigned stack_sz       = m_stack.size();
    unsigned stack_info_sz  = m_stack_info.size();
    unsigned call_stack_sz;
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        call_stack_sz       = m_call_stack.size();
    } else {
        call_stack_sz       = m_call_stack.size();
    }
    try {
        return optional<vm_obj>(invoke(fn, nargs, args));
    } catch (throwable const & ex) {
        m_code           = code;
        m_fn_idx         = fn_idx;
        m_pc             = pc;
        m_bp             = bp;
        m_next_frame_idx = next_frame_idx;
        m_stack.resize(stack_sz);
        m_stack_info.resize(stack_info_sz);
        if (m_profiling) {
            unique_lock<mutex> lk(m_call_stack_mtx);
            while (m_call_stack.size() > call_stack_sz) m_call_stack.pop_back();
        } else {
            while (m_call_stack.size() > call_stack_sz) m_call_stack.pop_back();
        }
        return optional<vm_obj>();
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6, vm_obj const & a7);
vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8);
vm_obj native_invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args);

vm_obj invoke(vm_obj const & fn, vm_obj const & a1) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2, a3, a4);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3, a4);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2, a3, a4, a5);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3, a4, a5);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2, a3, a4, a5, a6);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2, a3, a4, a5, a6, a7);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6, a7);
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, a1, a2, a3, a4, a5, a6, a7, a8);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6, a7, a8);
    }
}

vm_obj invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    if (is_native_closure(fn)) {
        return native_invoke(fn, nargs, args);
    } else {
        lean_assert(g_vm_state);
        return g_vm_state->invoke(fn, nargs, args);
    }
}

vm_obj invoke(unsigned fn_idx, unsigned nargs, vm_obj const * args) {
    lean_assert(g_vm_state);
    vm_obj fn = mk_vm_closure(fn_idx, 0, nullptr);
    return invoke(fn, nargs, args);
}

vm_obj invoke(unsigned fn_idx, vm_obj const & arg) {
    return invoke(fn_idx, 1, &arg);
}

static vm_obj update_native_closure(vm_obj const & fn, unsigned num_new_args, vm_obj const * new_args) {
    vm_native_closure const * c = to_native_closure(fn);
    lean_assert(num_new_args < c->get_arity());
    return mk_native_closure(c->get_fn(), c->get_arity(), num_new_args, new_args);
}

static vm_obj update_native_closure(vm_obj const & fn, buffer<vm_obj> const & new_args) {
    return update_native_closure(fn, new_args.size(), new_args.data());
}

inline vm_cfunction_1 to_nfn1(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_1>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_2 to_nfn2(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_2>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_3 to_nfn3(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_3>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_4 to_nfn4(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_4>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_5 to_nfn5(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_5>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_6 to_nfn6(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_6>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_7 to_nfn7(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_7>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_8 to_nfn8(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_8>(to_native_closure(fn)->get_fn()); }
inline vm_cfunction_N to_nfnN(vm_obj const & fn) { return reinterpret_cast<vm_cfunction_N>(to_native_closure(fn)->get_fn()); }

static void append_native_args(vm_obj const & fn, buffer<vm_obj> & args) {
    lean_assert(is_native_closure(fn));
    vm_obj const * begin = to_native_closure(fn)->get_args();
    vm_obj const * end   = begin + to_native_closure(fn)->get_num_args();
    vm_obj const * it    = end;
    while (it != begin) {
        --it;
        args.push_back(*it);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 1;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else {
        switch (arity) {
        case 0: lean_unreachable();
        case 1: return to_nfn1(fn)(a1);
        case 2: return to_nfn2(fn)(args[0], a1);
        case 3: return to_nfn3(fn)(args[1], args[0], a1);
        case 4: return to_nfn4(fn)(args[2], args[1], args[0], a1);
        case 5: return to_nfn5(fn)(args[3], args[2], args[1], args[0], a1);
        case 6: return to_nfn6(fn)(args[4], args[3], args[2], args[1], args[0], a1);
        case 7: return to_nfn7(fn)(args[5], args[4], args[3], args[2], args[1], args[0], a1);
        case 8: return to_nfn8(fn)(args[6], args[5], args[4], args[3], args[2], args[1], args[0], a1);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 2;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: lean_unreachable();
        case 2: return to_nfn2(fn)(a1, a2);
        case 3: return to_nfn3(fn)(args[0], a1, a2);
        case 4: return to_nfn4(fn)(args[1], args[0], a1, a2);
        case 5: return to_nfn5(fn)(args[2], args[1], args[0], a1, a2);
        case 6: return to_nfn6(fn)(args[3], args[2], args[1], args[0], a1, a2);
        case 7: return to_nfn7(fn)(args[4], args[3], args[2], args[1], args[0], a1, a2);
        case 8: return to_nfn8(fn)(args[5], args[4], args[3], args[2], args[1], args[0], a1, a2);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else {
        lean_assert(new_nargs > arity);
        return invoke(native_invoke(fn, a1), a2);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 3;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: lean_unreachable();
        case 3: return to_nfn3(fn)(a1, a2, a3);
        case 4: return to_nfn4(fn)(args[0], a1, a2, a3);
        case 5: return to_nfn5(fn)(args[1], args[0], a1, a2, a3);
        case 6: return to_nfn6(fn)(args[2], args[1], args[0], a1, a2, a3);
        case 7: return to_nfn7(fn)(args[3], args[2], args[1], args[0], a1, a2, a3);
        case 8: return to_nfn8(fn)(args[4], args[3], args[2], args[1], args[0], a1, a2, a3);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2), a3);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 4;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a4);
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: case 3: lean_unreachable();
        case 4: return to_nfn4(fn)(a1, a2, a3, a4);
        case 5: return to_nfn5(fn)(args[0], a1, a2, a3, a4);
        case 6: return to_nfn6(fn)(args[1], args[0], a1, a2, a3, a4);
        case 7: return to_nfn7(fn)(args[2], args[1], args[0], a1, a2, a3, a4);
        case 8: return to_nfn8(fn)(args[3], args[2], args[1], args[0], a1, a2, a3, a4);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            new_args.push_back(a4);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2, a3), a4);
    } else if (new_nargs == arity + 2) {
        return invoke(native_invoke(fn, a1, a2), a3, a4);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3, a4);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 5;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a5);
        new_args.push_back(a4);
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: case 3: case 4: lean_unreachable();
        case 5: return to_nfn5(fn)(a1, a2, a3, a4, a5);
        case 6: return to_nfn6(fn)(args[0], a1, a2, a3, a4, a5);
        case 7: return to_nfn7(fn)(args[1], args[0], a1, a2, a3, a4, a5);
        case 8: return to_nfn8(fn)(args[2], args[1], args[0], a1, a2, a3, a4, a5);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            new_args.push_back(a4);
            new_args.push_back(a5);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2, a3, a4), a5);
    } else if (new_nargs == arity + 2) {
        return invoke(native_invoke(fn, a1, a2, a3), a4, a5);
    } else if (new_nargs == arity + 3) {
        return invoke(native_invoke(fn, a1, a2), a3, a4, a5);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3, a4, a5);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 6;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a6);
        new_args.push_back(a5);
        new_args.push_back(a4);
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: case 3: case 4: case 5: lean_unreachable();
        case 6: return to_nfn6(fn)(a1, a2, a3, a4, a5, a6);
        case 7: return to_nfn7(fn)(args[0], a1, a2, a3, a4, a5, a6);
        case 8: return to_nfn8(fn)(args[1], args[0], a1, a2, a3, a4, a5, a6);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            new_args.push_back(a4);
            new_args.push_back(a5);
            new_args.push_back(a6);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5), a6);
    } else if (new_nargs == arity + 2) {
        return invoke(native_invoke(fn, a1, a2, a3, a4), a5, a6);
    } else if (new_nargs == arity + 3) {
        return invoke(native_invoke(fn, a1, a2, a3), a4, a5, a6);
    } else if (new_nargs == arity + 4) {
        return invoke(native_invoke(fn, a1, a2), a3, a4, a5, a6);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3, a4, a5, a6);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6, vm_obj const & a7) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 7;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a7);
        new_args.push_back(a6);
        new_args.push_back(a5);
        new_args.push_back(a4);
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: case 3: case 4: case 5: case 6: lean_unreachable();
        case 7: return to_nfn7(fn)(a1, a2, a3, a4, a5, a6, a7);
        case 8: return to_nfn8(fn)(args[0], a1, a2, a3, a4, a5, a6, a7);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            new_args.push_back(a4);
            new_args.push_back(a5);
            new_args.push_back(a6);
            new_args.push_back(a7);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5, a6), a7);
    } else if (new_nargs == arity + 2) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5), a6, a7);
    } else if (new_nargs == arity + 3) {
        return invoke(native_invoke(fn, a1, a2, a3, a4), a5, a6, a7);
    } else if (new_nargs == arity + 4) {
        return invoke(native_invoke(fn, a1, a2, a3), a4, a5, a6, a7);
    } else if (new_nargs == arity + 5) {
        return invoke(native_invoke(fn, a1, a2), a3, a4, a5, a6, a7);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3, a4, a5, a6, a7);
    }
}

vm_obj native_invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                     vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8) {
    vm_native_closure const * c = to_native_closure(fn);
    unsigned nargs      = c->get_num_args();
    vm_obj const * args = c->get_args();
    unsigned arity      = c->get_arity();
    unsigned new_nargs  = nargs + 8;
    if (new_nargs < arity) {
        buffer<vm_obj> new_args;
        new_args.push_back(a8);
        new_args.push_back(a7);
        new_args.push_back(a6);
        new_args.push_back(a5);
        new_args.push_back(a4);
        new_args.push_back(a3);
        new_args.push_back(a2);
        new_args.push_back(a1);
        new_args.append(nargs, args);
        return update_native_closure(fn, new_args);
    } else if (new_nargs == arity) {
        switch (arity) {
        case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7: lean_unreachable();
        case 8: return to_nfn8(fn)(a1, a2, a3, a4, a5, a6, a7, a8);
        default:
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.push_back(a1);
            new_args.push_back(a2);
            new_args.push_back(a3);
            new_args.push_back(a4);
            new_args.push_back(a5);
            new_args.push_back(a6);
            new_args.push_back(a7);
            new_args.push_back(a8);
            return to_nfnN(fn)(new_args.size(), new_args.data());
        }
    } else if (new_nargs == arity + 1) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5, a6, a7), a8);
    } else if (new_nargs == arity + 2) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5, a6), a7, a8);
    } else if (new_nargs == arity + 3) {
        return invoke(native_invoke(fn, a1, a2, a3, a4, a5), a6, a7, a8);
    } else if (new_nargs == arity + 4) {
        return invoke(native_invoke(fn, a1, a2, a3, a4), a5, a6, a7, a8);
    } else if (new_nargs == arity + 5) {
        return invoke(native_invoke(fn, a1, a2, a3), a4, a5, a6, a7, a8);
    } else if (new_nargs == arity + 6) {
        return invoke(native_invoke(fn, a1, a2), a3, a4, a5, a6, a7, a8);
    } else {
        return invoke(native_invoke(fn, a1), a2, a3, a4, a5, a6, a7, a8);
    }
}

vm_obj native_invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    if (nargs <= 8) {
        switch (nargs) {
        case 1: return native_invoke(fn, args[0]);
        case 2: return native_invoke(fn, args[0], args[1]);
        case 3: return native_invoke(fn, args[0], args[1], args[2]);
        case 4: return native_invoke(fn, args[0], args[1], args[2], args[3]);
        case 5: return native_invoke(fn, args[0], args[1], args[2], args[3], args[4]);
        case 6: return native_invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7: return native_invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        case 8: return native_invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
        default: lean_unreachable();
        }
    }
    vm_native_closure const * c = to_native_closure(fn);
    unsigned c_nargs      = c->get_num_args();
    vm_obj const * c_args = c->get_args();
    unsigned arity        = c->get_arity();
    unsigned new_c_nargs  = c_nargs + nargs;
    if (new_c_nargs < arity) {
        buffer<vm_obj> new_args;
        unsigned i = nargs;
        while (i > 0) { --i; new_args.push_back(args[i]); }
        new_args.append(c_nargs, c_args);
        return update_native_closure(fn, new_args);
    } else if (new_c_nargs == arity) {
        if (c_nargs == 0) {
            return to_nfnN(fn)(nargs, args);
        } else {
            buffer<vm_obj> new_args;
            append_native_args(fn, new_args);
            new_args.append(nargs, args);
            return to_nfnN(fn)(nargs, args);
        }
    } else {
        lean_assert(new_c_nargs > arity);
        buffer<vm_obj> new_args;
        buffer<vm_obj> rest_args;
        /* copy arity - csize(fn) arguments to new_args, and the rest to rest_args */
        lean_assert(c_nargs < arity);
        unsigned n = arity - c_nargs;
        lean_assert(n > 1);
        lean_assert(n < nargs);
        new_args.append(n, args);
        rest_args.append(nargs - n, args + n);
        return invoke(native_invoke(fn, new_args.size(), new_args.data()), rest_args.size(), rest_args.data());
    }
}

vm_state & get_vm_state() {
    lean_assert(g_vm_state);
    return *g_vm_state;
}

void vm_state::push_local_info(unsigned idx, vm_local_info const & info) {
    unsigned min_sz = m_bp + idx + 1;
    if (m_stack_info.size() < min_sz)
        m_stack_info.resize(min_sz);
    m_stack_info[m_bp+idx] = info;
}

void vm_state::push_frame_core(unsigned num, unsigned next_pc, unsigned next_fn_idx) {
    m_call_stack.emplace_back(m_code, m_fn_idx, num, next_pc, m_bp, next_fn_idx, m_next_frame_idx);
    m_next_frame_idx++;
    m_fn_idx = next_fn_idx;
}

void vm_state::push_frame(unsigned num, unsigned next_pc, unsigned next_fn_idx) {
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        push_frame_core(num, next_pc, next_fn_idx);
    } else {
        push_frame_core(num, next_pc, next_fn_idx);
    }
}

unsigned vm_state::pop_frame_core() {
    lean_assert(!m_call_stack.empty());
    frame const & fr = m_call_stack.back();
    unsigned sz      = m_stack.size();
    lean_assert(sz - fr.m_num - 1 < m_stack.size());
    lean_assert(sz - 1 < m_stack.size());
    swap(m_stack[sz - fr.m_num - 1], m_stack[sz - 1]);
    m_stack.resize(sz - fr.m_num);
    unsigned curr_fidx = fr.m_curr_fn_idx;
    if (curr_fidx != g_null_fn_idx && get_decl(curr_fidx).get_arity() == 0) {
        /* cache result */
        if (curr_fidx >= m_cache_vector.size())
            m_cache_vector.resize(curr_fidx+1);
        m_cache_vector[curr_fidx] = m_stack.back();
    }
    if (m_debugging) shrink_stack_info();
    m_code   = fr.m_code;
    m_fn_idx = fr.m_fn_idx;
    m_pc     = fr.m_pc;
    m_bp     = fr.m_bp;
    unsigned stack_sz = m_call_stack.size();
    m_call_stack.pop_back();
    return stack_sz;
}

unsigned vm_state::pop_frame() {
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        return pop_frame_core();
    } else {
        return pop_frame_core();
    }
}

void vm_state::invoke_global(vm_decl const & d) {
    push_frame(d.get_arity(), m_pc+1, d.get_idx());
    m_code            = d.get_code();
    m_pc              = 0;
    m_bp              = m_stack.size() - d.get_arity();
    if (m_debugging) {
        m_stack_info.resize(m_stack.size());
        unsigned i = 0;
        for (auto const & info : d.get_args_info()) {
            m_stack_info[m_bp + i] = info;
            i++;
        }
    }
#if 0
    std::cout << d.get_name() << "\n";
    for (auto info : d.get_args_info()) {
        std::cout << info.first << " : ";
        if (info.second)
            std::cout << *info.second;
        else
            std::cout << "none";
        std::cout << "\n";
    }
    std::cout << "----------\n";
    display_stack(std::cout);
    std::cout << "============\n";
#endif
}

void vm_state::invoke_cfun(vm_decl const & d) {
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        push_frame_core(0, 0, d.get_idx());
    }
    invoke_fn(d.get_cfn(), d.get_arity());
    if (m_profiling) {
        unique_lock<mutex> lk(m_call_stack_mtx);
        m_call_stack.pop_back();
    }
}

void vm_state::invoke(vm_decl const & d) {
    switch (d.kind()) {
    case vm_decl_kind::Bytecode:
        invoke_global(d); break;
    case vm_decl_kind::Builtin:
        invoke_builtin(d); break;
    case vm_decl_kind::CFun:
        invoke_cfun(d); break;
    }
}

void vm_state::display_stack(std::ostream & out) const {
    for (unsigned i = 0; i < m_stack.size(); i++) {
        if (i == m_bp)
            out << "[bp] ";
        else
            out << "     ";
        display(out, m_stack[i]);
        if (m_debugging && i < m_stack_info.size() && !m_stack_info[i].first.is_anonymous()) {
            out << ", " << m_stack_info[i].first;
            if (m_stack_info[i].second)
                out << " : " << *m_stack_info[i].second;
        }
        out << "\n";
    }
    if (m_bp == m_stack.size())
        out << "[bp]\n";
}

void vm_state::display_call_stack(std::ostream & out) const {
    for (frame const & fr : m_call_stack) {
        out << ">> (fn_idx := " << fr.m_fn_idx << ", num := " << fr.m_num << ", pc := " << fr.m_pc << ", bp: " << fr.m_bp << ")\n";
    }
}

void vm_state::display_registers(std::ostream & out) const {
    out << "pc: " << m_pc << ", bp: " << m_bp << "\n";
}

void vm_state::run() {
    lean_assert(m_code);
    unsigned init_call_stack_sz = m_call_stack.size();
    m_pc = 0;
    while (true) {
      main_loop:
        if (LEAN_UNLIKELY(m_debugging)) {
            debugger_step();
        }
        vm_instr const & instr = m_code[m_pc];
        DEBUG_CODE({
                /* We only trace VM in debug mode */
                lean_trace(name({"vm", "run"}),
                           tout() << m_pc << ": ";
                           instr.display(tout().get_stream());
                           tout() << "\n";
                           display_stack(tout().get_stream());
                           tout() << "\n";)
                    });
        switch (instr.op()) {
        case opcode::Push:
            /* Instruction: push i

               stack before,      after
               ...                ...
               bp :  a_0          bp :  a_0
               ...                ...
               a_i  ==>           a_i
               ...                ...
               v                  v
                                  a_i
            */
            m_stack.push_back(m_stack[m_bp + instr.get_idx()]);
            m_pc++;
            goto main_loop;
        case opcode::Move: {
            /* Instruction: move i

               stack before,      after
               ...                ...
               bp :  a_0          bp :  a_0
               ...                ...
               a_i  ==>           #0
               ...                ...
               v                  v
                                  a_i
            */
            unsigned off = m_bp + instr.get_idx();
            lean_vm_check(off < m_stack.size());
            if (LEAN_UNLIKELY(m_debugging)) {
                m_stack.push_back(m_stack[off]);
            } else {
                m_stack.push_back(mk_vm_unit());
                swap(m_stack.back(), m_stack[off]);
            }
            m_pc++;
            goto main_loop;
        }
        case opcode::Drop: {
            /* Instruction: drop n

               stack before,      after
               ...                ...
               w                  w
               a_1   ==>          v
               ...
               a_n
               v
            */
            unsigned num = instr.get_num();
            unsigned sz  = m_stack.size();
            lean_vm_check(sz > num);
            swap(m_stack[sz - num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - num);
            if (m_debugging) shrink_stack_info();
            m_pc++;
            goto main_loop;
        }
        case opcode::Goto:
            /* Instruction: goto pc

               m_pc := pc
            */
            m_pc = instr.get_goto_pc();
            goto main_loop;
        case opcode::SConstructor:
            /** Instruction: scnstr i

                stack before,      after
                ...                ...
                v    ==>           v
                #i
            */
            m_stack.push_back(mk_vm_simple(instr.get_cidx()));
            m_pc++;
            goto main_loop;
        case opcode::Constructor: {
            /** Instruction: cnstr i n

                stack before,      after
                ...                ...
                v      ==>         v
                a_1                (#i a_1 ... a_n)
                ...
                a_n
            */
            unsigned nfields = instr.get_nfields();
            unsigned sz      = m_stack.size();
            lean_vm_check(nfields <= sz);
            vm_obj new_value = mk_vm_constructor(instr.get_cidx(), nfields, m_stack.data() + sz - nfields);
            m_stack.resize(sz - nfields + 1);
            swap(m_stack.back(), new_value);
            if (m_debugging) shrink_stack_info();
            m_pc++;
            goto main_loop;
        }
        case opcode::Closure: {
            /** Instruction: closure fn n

                stack before,      after
                ...                ...
                v      ==>         v
                a_n                (fn a_n ... a_1)
                ...
                a_1
            */
            unsigned nargs     = instr.get_nargs();
            unsigned sz        = m_stack.size();
            lean_vm_check(nargs <= sz);
            vm_obj new_value   = mk_vm_closure(instr.get_fn_idx(), nargs, m_stack.data() + sz - nargs);
            m_stack.resize(sz - nargs + 1);
            swap(m_stack.back(), new_value);
            if (m_debugging) shrink_stack_info();
            m_pc++;
            goto main_loop;
        }
        case opcode::Num:
            /** Instruction: num n

                stack before,      after
                ...                ...
                v    ==>           v
                                   n
            */
            m_stack.push_back(mk_vm_mpz(instr.get_mpz()));
            m_pc++;
            goto main_loop;
        case opcode::Expr:
            /** Instruction: pexpr e

                stack before,      after
                ...                ...
                v    ==>           v
                                   e
            */
            m_stack.push_back(to_obj(instr.get_expr()));
            m_pc++;
            goto main_loop;
        case opcode::LocalInfo:
            if (m_debugging)
                push_local_info(instr.get_local_idx(), instr.get_local_info());
            m_pc++;
            goto main_loop;
        case opcode::Destruct: {
            /** Instruction: destruct

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                ...
                a_n
            */
            vm_obj top = m_stack.back();
            stack_pop_back();
            push_fields(top);
            m_pc++;
            goto main_loop;
        }
        case opcode::Cases2: {
            /** Instruction: cases2 pc1 pc2

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                ...
                a_n

                m_pc := pc1  if  i == 0
                := pc2  if  i == 1
            */
            vm_obj top = m_stack.back();
            stack_pop_back();
            push_fields(top);
            m_pc = instr.get_cases2_pc(cidx(top));
            goto main_loop;
        }
        case opcode::NatCases: {
            /** Instruction: natcases pc1 pc2

                stack before,              after (if n = 0)    after (if n > 0)
                ...                        ...                 ...
                v                 ==>      v                   v
                n                                              n-1

                m_pc := pc1  if  n == 0
                := pc2  if  otherwise
            */
            vm_obj & top = m_stack.back();
            if (is_simple(top)) {
                unsigned val = cidx(top);
                if (val == 0) {
                    stack_pop_back();
                    m_pc++;
                    goto main_loop;
                } else {
                    vm_obj new_value = mk_vm_simple(val - 1);
                    swap(top, new_value);
                    m_pc = instr.get_cases2_pc(1);
                    goto main_loop;
                }
            } else {
                /* to_mpz checks lean_vm_check(is_mpz(top)) */
                mpz const & val = to_mpz(top);
                if (val == 0) {
                    stack_pop_back();
                    m_pc++;
                    goto main_loop;
                } else {
                    vm_obj new_value = mk_vm_mpz(val - 1);
                    swap(top, new_value);
                    m_pc = instr.get_cases2_pc(1);
                    goto main_loop;
                }
            }
        }
        case opcode::CasesN: {
            /** Instruction: casesn pc_0 ... pc_[n-1]

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                                           ...
                                           a_n

                m_pc := pc_i
            */
            vm_obj top = m_stack.back();
            stack_pop_back();
            push_fields(top);
            m_pc = instr.get_casesn_pc(cidx(top));
            goto main_loop;
        }
        case opcode::BuiltinCases: {
            /** Instruction: builtin_cases
                It is similar to CasesN, but uses the vm_cases_function to extract the data.
            */
            vm_obj top = m_stack.back();
            stack_pop_back();
            vm_cases_function fn = get_builtin_cases(instr.get_cases_idx());
            buffer<vm_obj> data;
            unsigned cidx = fn(top, data);
            std::copy(data.begin(), data.end(), std::back_inserter(m_stack));
            m_pc = instr.get_casesn_pc(cidx);
            goto main_loop;
        }
        case opcode::Proj: {
            /** Instruction: proj i

               stack before,              after
               ...                        ...
               v                     ==>  v
               (#i a_0 ... a_{n-1})       a_i

            */
            vm_obj & top = m_stack.back();
            top = cfield(top, instr.get_idx());
            m_pc++;
            goto main_loop;
        }
        case opcode::Unreachable:
            throw exception("VM unreachable instruction has been reached");
        case opcode::Ret:
            /**
               Instruction: ret

               call stack before                  after

               ...                                ...
               (code, fn_idx, num, pc, bp)  ==>

               Restore m_code, m_fn_idx, m_pc, m_bp with top of call stack.

               stack before        after
               ...                 ...
               v                   v
               a_n                 r
               ...       ==>
               a_1
               r


               a_1, ... a_n were the arguments for the function call.
               r is the result.
            */
            if (pop_frame() == init_call_stack_sz)
                return;
            else
                goto main_loop;
        case opcode::Apply: {
            /**
               Instruction: apply

               We keep consuming 'apply' instructions until the next instruction is not an 'apply'
               or we have enough arguments for executing the closure.

               stack before
               ...
               v
               a_n
               ...                       ==>
               a_1
               (closure fn b_m ... b_1)

               Case 1)
               Suppose we have n consecutive 'apply' instructions and arity of fn < n+m


               Then,

               stack after
                                       ...
               =>                      v
                                       (closure fn a_n ... a_1 b_m ... b_1)

               Case 2) arity of fn = n + m
               Then, see InvokeGlobal (if fn is global) and InvokeBuiltin (if fn is builtin)
            */
            unsigned sz       = m_stack.size();
            vm_obj closure    = m_stack.back();
            stack_pop_back();
            // TODO(Leo): remove redundant code. The following two branches in the if-then-else statement are very similar.
            if (is_simple(closure)) {
                lean_vm_check(cidx(closure) == 0);
                stack_pop_back();
                m_stack.push_back(closure);
                m_pc++;
                goto main_loop;
            } else if (is_native_closure(closure)) {
                vm_native_closure const * c = to_native_closure(closure);
                unsigned arity              = c->get_arity();
                unsigned nargs              = c->get_num_args() + 1;
                lean_assert(nargs <= arity);
                /* Keep consuming 'apply' instructions while nargs < arity */
                while (nargs < arity && m_code[m_pc+1].op() == opcode::Apply) {
                    nargs++;
                    m_pc++;
                }
                /* Copy closure data to the top of the stack */
                std::copy(c->get_args(), c->get_args() + c->get_num_args(), std::back_inserter(m_stack));
                if (nargs < arity) {
                    /* Case 1) We don't have sufficient arguments. So, we create a new closure */
                    sz = m_stack.size();
                    vm_obj new_value = update_native_closure(closure, nargs, m_stack.data() + sz - nargs);
                    m_stack.resize(sz - nargs + 1);
                    swap(m_stack.back(), new_value);
                    if (m_debugging) shrink_stack_info();
                    m_pc++;
                    goto main_loop;
                } else {
                    lean_assert(nargs == arity);
                    buffer<vm_obj> args;
                    /* Case 2 */
                    invoke_fn(c->get_fn(), arity);
                    goto main_loop;
                }
            } else {
                unsigned fn_idx   = cfn_idx(closure);
                vm_decl d         = get_decl(fn_idx);
                unsigned csz      = csize(closure);
                unsigned arity    = d.get_arity();
                lean_vm_check(csz < arity);
                unsigned nargs    = csz + 1;
                lean_vm_check(nargs <= arity);
                /* Keep consuming 'apply' instructions while nargs < arity */
                while (nargs < arity && m_code[m_pc+1].op() == opcode::Apply) {
                    nargs++;
                    m_pc++;
                }
                /* Copy closure data to the top of the stack */
                std::copy(cfields(closure), cfields(closure) + csz, std::back_inserter(m_stack));
                if (nargs < arity) {
                    /* Case 1) We don't have sufficient arguments. So, we create a new closure */
                    sz = m_stack.size();
                    vm_obj new_value = mk_vm_closure(fn_idx, nargs, m_stack.data() + sz - nargs);
                    m_stack.resize(sz - nargs + 1);
                    swap(m_stack.back(), new_value);
                    if (m_debugging) shrink_stack_info();
                    m_pc++;
                    goto main_loop;
                } else {
                    lean_assert(nargs == arity);
                    /* Case 2 */
                    invoke(d);
                    goto main_loop;
                }
            }
        }
        case opcode::InvokeGlobal: {
            check_interrupted();
            check_heartbeat();
            check_memory("vm");
            /**
               Instruction: ginvoke fn

               call stack before                  after

               ...              ==>               ...
                                                  (fn.m_code, fn.idx, fn.arity, m_pc+1, m_bp)

               Update m_code, m_fn_idx, with fn, and update m_pc := 0, m_bp

               stack before            after
               ...                     ...
               v                       v
               a_n              m_bp : a_n
               ...       ==>           ...
               a_1                     a_1

               where n is fn.arity
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            /* If d is 0-ary, then check if value is cached */
            if (decl.get_arity() == 0 && decl.get_idx() < m_cache_vector.size()) {
                if (auto r = m_cache_vector[decl.get_idx()]) {
                    m_stack.push_back(*r);
                    m_pc++;
                    goto main_loop;
                }
            }
            invoke_global(decl);
            goto main_loop;
        }
        case opcode::InvokeBuiltin: {
            check_interrupted();
            check_heartbeat();
            check_memory("vm");
            /**
               Instruction: builtin fn

               stack before          after
               ...                   ...
               v                     v
               a_n                   r
               ...       ==>
               a_1

               where n is fn.arity

               Remark: note that the arguments are in reverse order.
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            invoke_builtin(decl);
            goto main_loop;
        }
        case opcode::InvokeCFun: {
            check_interrupted();
            check_heartbeat();
            check_memory("vm");
            /**
               Instruction: cfun fn

               Similar to InvokeBuiltin
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            invoke_cfun(decl);
            goto main_loop;
        }}
    }
}

void vm_state::invoke_fn(name const & fn) {
    auto idx = get_vm_index(fn);
    if (m_decl_map.contains(idx)) {
        invoke_fn(idx);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

void vm_state::invoke_fn(unsigned fn_idx) {
    vm_decl d      = get_decl(fn_idx);
    unsigned arity = d.get_arity();
    if (arity > m_stack.size())
        throw exception("invalid VM function call, data stack does not have enough values");
    invoke(d);
    run();
}

vm_obj vm_state::get_constant(name const & cname) {
    auto fn_idx = get_vm_index(cname);
    if (m_decl_map.contains(fn_idx)) {
        vm_decl d = get_decl(fn_idx);
        if (d.get_arity() == 0) {
            DEBUG_CODE(unsigned stack_sz = m_stack.size(););
            unsigned saved_pc = m_pc;
            invoke(d);
            run();
            vm_obj r = m_stack.back();
            stack_pop_back();
            m_pc = saved_pc;
            lean_assert(m_stack.size() == stack_sz);
            return r;
        } else {
            return mk_vm_closure(fn_idx, 0, nullptr);
        }
    } else {
        throw exception(sstream() << "VM does not have code for '" << cname << "'");
    }
}

void vm_state::execute(vm_instr const * code) {
    push_frame(0, m_pc, g_null_fn_idx);
    m_code            = code;
    m_pc              = 0;
    m_bp              = m_stack.size();
    run();
}

void vm_state::apply(unsigned n) {
    buffer<vm_instr> code;
    for (unsigned i = 0; i < n; i++)
        code.push_back(mk_apply_instr());
    code.push_back(mk_ret_instr());
    execute(code.data());
}

void vm_state::display(std::ostream & out, vm_obj const & o) const {
    ::lean::display(out, o);
}

optional<vm_decl> vm_state::get_decl(name const & n) const {
    auto idx = get_vm_index(n);
    if (m_decl_map.contains(idx))
        return optional<vm_decl>(get_decl(idx));
    else
        return optional<vm_decl>();
}

optional<name> vm_state::curr_fn() const {
    if (m_fn_idx == g_null_fn_idx)
        return optional<name>();
    else
        return optional<name>(m_decl_map.find(m_fn_idx)->get_name());
}
#if defined(LEAN_MULTI_THREAD)
static name * g_profiler_freq = nullptr;

unsigned get_profiler_freq(options const & opts) {
    return opts.get_unsigned(*g_profiler_freq, LEAN_DEFAULT_PROFILER_FREQ);
}
#endif

vm_state::profiler::profiler(vm_state & s, options const & opts):
    m_state(s),
    m_stop(false),
#if defined(LEAN_MULTI_THREAD)
    m_freq_ms(get_profiler_freq(opts)),
    m_thread_ptr(get_profiler(opts) ?
        new interruptible_thread([&]() {
                chrono::milliseconds d(m_freq_ms);
                bool first = true;
                auto start = chrono::steady_clock::now();
                while (!m_stop) {
                    if (first) {
                        first = false;
                    } else {
                        unique_lock<mutex> lk(m_state.m_call_stack_mtx);
                        auto curr = chrono::steady_clock::now();
                        m_snapshots.push_back(snapshot_core());
                        snapshot_core & s = m_snapshots.back();
                        s.m_perf_counters = m_state.get_perf_counters();
                        s.m_duration      = chrono::duration_cast<chrono::milliseconds>(curr - start);
                        for (frame const & fr : m_state.m_call_stack) {
                            if (fr.m_curr_fn_idx != g_null_fn_idx &&
                                (s.m_stack.empty() || s.m_stack.back().first != fr.m_curr_fn_idx)) {
                                s.m_stack.emplace_back(fr.m_curr_fn_idx, fr.m_frame_idx);
                            }
                        }
                    }
                    start = chrono::steady_clock::now();
                    this_thread::sleep_for(d);
                }
            }) :
        nullptr)
#else
    m_freq_ms(0),
    m_thread_ptr(nullptr)
#endif
{
#if defined(LEAN_MULTI_THREAD)
    m_state.m_profiling = get_profiler(opts);
#endif
}

void vm_state::profiler::stop() {
    if (!m_stop && m_thread_ptr) {
        m_stop = true;
        m_thread_ptr->join();
        m_state.m_profiling = false;
    }
}

vm_state::profiler::~profiler() {
    stop();
}

auto vm_state::profiler::get_snapshots() -> snapshots {
    stop();
    snapshots r;
    r.m_total_time = chrono::milliseconds(0);
    std::unordered_map<name, chrono::milliseconds, name_hash> cum_times;
    for (snapshot_core const & s : m_snapshots) {
        snapshot new_s;
        new_s.m_duration       = s.m_duration;
        new_s.m_perf_counters  = s.m_perf_counters;
        r.m_total_time        += s.m_duration;
        auto & new_stack = new_s.m_stack;
        std::unordered_set<name, name_hash> decl_already_seen_in_this_stack;
        for (auto const & p : s.m_stack) {
            vm_decl const * decl = m_state.m_decl_map.find(p.first);
            lean_assert(decl);
            name decl_name = decl->get_name();
            /* Remove unnecessary suffixes. */
            while (true) {
                if (decl_name.is_atomic()) break;
                if (!decl_name.is_string()) break;
                char const * str = decl_name.get_string();
                if (str[0] != '_') break;
                if (strncmp(str, "_lambda", 7) == 0) break;
                decl_name = decl_name.get_prefix();
            }
            if (auto prv = hidden_to_user_name(m_state.env(), decl_name))
                decl_name = *prv;
            if (new_stack.empty() || decl_name != new_stack.back().first)
                new_stack.emplace_back(decl_name, p.second);

            if (decl_already_seen_in_this_stack.insert(decl_name).second) {
                // not seen before in this stack
                cum_times[decl_name] += s.m_duration;
            }
        }
        r.m_snapshots.push_back(new_s);
    }

    for (auto & cum_time_entry : cum_times) r.m_cum_times.push_back(cum_time_entry);
    std::sort(r.m_cum_times.begin(), r.m_cum_times.end(),
              [] (pair<name, chrono::milliseconds> & a, pair<name, chrono::milliseconds> & b) {
                  return b.second < a.second; });

    return r;
}

#if 0
static bool equal_fns(vm_state::profiler::snapshot const & s1, vm_state::profiler::snapshot const & s2) {
    if (s1.m_stack.size() != s2.m_stack.size()) return false;
    for (unsigned i = 0; i < s1.m_stack.size(); i++) {
        if (s1.m_stack[i].first != s2.m_stack[i].first)
            return false;
    }
    return true;
}
#endif

void vm_state::profiler::snapshots::display(std::ostream & out) const {
    if (!m_snapshots.empty()) {
        performance_counters const & c = m_snapshots.back().m_perf_counters;
        if (c.m_num_constructor_allocs > 0)
            out << "num. allocated objects:  " << c.m_num_constructor_allocs << "\n";
        if (c.m_num_closure_allocs > 0)
            out << "num. allocated closures: " << c.m_num_closure_allocs << "\n";
        if (c.m_num_mpz_allocs > 0)
            out << "num. allocated big nums: " << c.m_num_mpz_allocs << "\n";
    }
    for (auto & cum_time : m_cum_times) {
        out << std::setw(5) << cum_time.second.count() << "ms   "
            << std::setw(5) << std::fixed << std::setprecision(1)
            << (100.0f * cum_time.second.count()) / m_total_time.count() << "%   "
            << cum_time.first << "\n";
    }
#if 0
    unsigned i = 0;
    while (i < m_snapshots.size()) {
        snapshot const & s = m_snapshots[i];
        unsigned j = i+1;
        auto d = s.m_duration;
        for (; j < m_snapshots.size(); j++) {
            if (!equal_fns(s, m_snapshots[j]))
                break;
            d += m_snapshots[j].m_duration;
        }
        i = j;
        out << d.count() << ":";
        for (auto const & p : s.m_stack) {
            out << " " << p.first;
        }
        out << "\n";
    }
#endif
}

bool vm_state::profiler::snapshots::display(std::string const &what, options const &opts, std::ostream &out) const {
    report_profiling_time(what + " execution", m_total_time);
    if (m_total_time >= get_profiling_threshold(opts)) {
        out << what << " execution took " << display_profiling_time{m_total_time} << "\n";
        display(out);
        return true;
    } else {
        return false;
    }
}

void display_vm_code(std::ostream & out, unsigned code_sz, vm_instr const * code) {
    for (unsigned i = 0; i < code_sz; i++) {
        out << i << ": ";
        code[i].display(out);
        out << "\n";
    }
}

char const * get_vm_builtin_internal_name(name const & fn) {
    if (auto p = g_vm_builtins->find(fn))
        return std::get<1>(*p);
    if (auto p = g_vm_cbuiltins->find(fn))
        return std::get<1>(*p);
    if (auto p = g_vm_cases_builtins->find(fn))
        return std::get<0>(*p);
    return nullptr;
}

vm_builtin_kind get_vm_builtin_kind(name const & fn) {
    if (g_vm_builtins->contains(fn))
        return vm_builtin_kind::VMFun;
    if (g_vm_cbuiltins->contains(fn))
        return vm_builtin_kind::CFun;
    if (g_vm_cases_builtins->contains(fn))
        return vm_builtin_kind::Cases;
    lean_unreachable();
}

unsigned get_vm_builtin_arity(name const & fn) {
    if (auto p = g_vm_cbuiltins->find(fn))
        return std::get<0>(*p);
    lean_unreachable();
}

environment vm_monitor_register(environment const & env, name const & d) {
    expr const & type = env.get(d).get_type();
    if (!is_app_of(type, get_vm_monitor_name(), 1))
        throw exception("invalid vm_monitor.register argument, must be name of a definition of type (vm_monitor ?s) ");
    return module::add_and_perform(env, std::make_shared<vm_monitor_modification>(d));
}

[[noreturn]] void vm_check_failed(char const * condition) {
    throw exception(sstream() << "vm check failed: " << condition
                              << " (possibly due to incorrect axioms, or sorry)");
}

class vm_index_manager {
    shared_mutex m_mutex;
    std::unordered_map<name, unsigned, name_hash> m_name2idx;
    std::vector<name> m_idx2name;

public:
    unsigned get_index(name const & n) {
        {
            shared_lock lock(m_mutex);
            auto it = m_name2idx.find(n);
            if (it != m_name2idx.end())
                return it->second;
        }
        {
            exclusive_lock lock(m_mutex);
            auto it = m_name2idx.find(n);
            if (it != m_name2idx.end()) {
                return it->second;
            } else {
                auto i = static_cast<unsigned>(m_idx2name.size());
                m_idx2name.push_back(n);
                m_name2idx[n] = i;
                return i;
            }
        }
    }

    unsigned get_index_bound() {
        shared_lock _(m_mutex);
        return static_cast<unsigned>(m_idx2name.size());
    }

    name get_name(unsigned idx) {
        shared_lock lock(m_mutex);
        lean_assert(idx < m_idx2name.size());
        return m_idx2name.at(idx);
    }

    optional<name> find_name(unsigned idx) {
        shared_lock lock(m_mutex);
        if (idx < m_idx2name.size()) {
            return optional<name>(m_idx2name.at(idx));
        } else {
            return optional<name>();
        }
    }
};
static vm_index_manager * g_vm_index_manager = nullptr;

unsigned get_vm_index(name const & n) {
    return g_vm_index_manager->get_index(n);
}
unsigned get_vm_index_bound() {
    return g_vm_index_manager->get_index_bound();
}
name get_vm_name(unsigned idx) {
    return g_vm_index_manager->get_name(idx);
}
optional<name> find_vm_name(unsigned idx) {
    return g_vm_index_manager->find_name(idx);
}

void initialize_vm_core() {
    g_vm_index_manager = new vm_index_manager;
    g_vm_builtins = new name_map<std::tuple<unsigned, char const *, vm_function>>();
    g_vm_cbuiltins = new name_map<std::tuple<unsigned, char const *, vm_cfunction>>();
    g_vm_cases_builtins = new name_map<std::tuple<char const *, vm_cases_function>>();
    g_may_update_vm_builtins = true;
    DEBUG_CODE({
            /* We only trace VM in debug mode because it produces a 10% performance penalty */
            register_trace_class("vm");
            register_trace_class({"vm", "run"});
        });
}

void finalize_vm_core() {
    delete g_vm_builtins;
    delete g_vm_cbuiltins;
    delete g_vm_cases_builtins;
    delete g_vm_index_manager;
}

void initialize_vm() {
    g_ext = new vm_decls_reg();
    // g_may_update_vm_builtins = false;
    vm_reserve_modification::init();
    vm_code_modification::init();
    vm_monitor_modification::init();
#if defined(LEAN_MULTI_THREAD)
    g_profiler_freq  = new name{"profiler", "freq"};
    register_unsigned_option(*g_profiler_freq, LEAN_DEFAULT_PROFILER_FREQ, "(profiler) sampling frequency in milliseconds");
#endif
    g_debugger       = new name{"debugger"};
    register_bool_option(*g_debugger, false, "(debugger) debug code using VM monitors");
    /* TODO(Leo): move to .lean after we add primitives for creating new options on .lean files */
    register_bool_option(name({"debugger", "autorun"}), false,
                         "(debugger) skip debugger startup messages and initial prompt");
}

void finalize_vm() {
    delete g_ext;
    vm_reserve_modification::finalize();
    vm_code_modification::finalize();
    vm_monitor_modification::finalize();
#if defined(LEAN_MULTI_THREAD)
    delete g_profiler_freq;
#endif
    delete g_debugger;
}
}

void print(lean::vm_obj const & o) {
    ::lean::display(std::cout, o);
    std::cout << "\n";
}
