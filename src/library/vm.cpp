/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm.h"

namespace lean {
void vm_obj_cell::dec_ref(vm_obj & o, buffer<vm_obj_cell*> & todelete) {
    if (LEAN_VM_IS_PTR(o.m_data)) {
        vm_obj_cell * c = o.steal_ptr();
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_1, sizeof(vm_composite) + sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_2, sizeof(vm_composite) + 2*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_3, sizeof(vm_composite) + 3*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_4, sizeof(vm_composite) + 4*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_5, sizeof(vm_composite) + 5*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_6, sizeof(vm_composite) + 6*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_7, sizeof(vm_composite) + 7*sizeof(vm_obj));
DEF_THREAD_MEMORY_POOL(get_vm_composite_allocator_8, sizeof(vm_composite) + 8*sizeof(vm_obj));

vm_composite::vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data):
    vm_obj_cell(k), m_idx(idx),  m_size(sz) {
    vm_obj * fields = get_field_ptr();
    for (unsigned i = 0; i < sz; i++)
        fields[i] = data[i];
}

static vm_obj mk_vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data) {
    lean_assert(k == vm_obj_kind::Constructor || k == vm_obj_kind::Closure);
    switch (sz) {
    case 1: return vm_obj(new (get_vm_composite_allocator_1().allocate()) vm_composite(k, idx, sz, data));
    case 2: return vm_obj(new (get_vm_composite_allocator_2().allocate()) vm_composite(k, idx, sz, data));
    case 3: return vm_obj(new (get_vm_composite_allocator_3().allocate()) vm_composite(k, idx, sz, data));
    case 4: return vm_obj(new (get_vm_composite_allocator_4().allocate()) vm_composite(k, idx, sz, data));
    case 5: return vm_obj(new (get_vm_composite_allocator_5().allocate()) vm_composite(k, idx, sz, data));
    case 6: return vm_obj(new (get_vm_composite_allocator_6().allocate()) vm_composite(k, idx, sz, data));
    case 7: return vm_obj(new (get_vm_composite_allocator_7().allocate()) vm_composite(k, idx, sz, data));
    case 8: return vm_obj(new (get_vm_composite_allocator_8().allocate()) vm_composite(k, idx, sz, data));
    default:
        char * mem = new char[sizeof(vm_composite) + sz * sizeof(vm_obj)];
        return vm_obj(new (mem) vm_composite(k, idx, sz, data));
    }
}

void vm_composite::dealloc(buffer<vm_obj_cell*> & todelete) {
    unsigned sz = m_size;
    vm_obj * fields = get_field_ptr();
    for (unsigned i = 0; i < sz; i++) {
        dec_ref(fields[i], todelete);
    }
    this->~vm_composite();
    switch (sz) {
    case 1: get_vm_composite_allocator_1().recycle(this); break;
    case 2: get_vm_composite_allocator_2().recycle(this); break;
    case 3: get_vm_composite_allocator_3().recycle(this); break;
    case 4: get_vm_composite_allocator_4().recycle(this); break;
    case 5: get_vm_composite_allocator_5().recycle(this); break;
    case 6: get_vm_composite_allocator_6().recycle(this); break;
    case 7: get_vm_composite_allocator_7().recycle(this); break;
    case 8: get_vm_composite_allocator_8().recycle(this); break;
    default: delete[] reinterpret_cast<char*>(this); break;
    }
}

vm_obj mk_vm_constructor(unsigned cidx, unsigned sz, vm_obj const * data) {
    return mk_vm_composite(vm_obj_kind::Constructor, cidx, sz, data);
}

vm_obj mk_vm_closure(unsigned fn_idx, unsigned sz, vm_obj const * data) {
    return mk_vm_composite(vm_obj_kind::Closure, fn_idx, sz, data);
}

DEF_THREAD_MEMORY_POOL(get_vm_mpz_allocator, sizeof(vm_mpz));

vm_mpz::vm_mpz(mpz const & v):
    vm_obj_cell(vm_obj_kind::MPZ),
    m_value(v) {
}

vm_obj mk_vm_mpz(mpz const & v) {
    return vm_obj(new (get_vm_mpz_allocator().allocate()) vm_mpz(v));
}

void vm_mpz::dealloc() {
    this->~vm_mpz();
    get_vm_mpz_allocator().recycle(this);
}

vm_obj mk_vm_external(vm_external * cell) {
    lean_assert(cell);
    lean_assert(cell->get_rc() == 0);
    return vm_obj(cell);
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
            case vm_obj_kind::Simple:      lean_unreachable();
            case vm_obj_kind::Constructor: to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::Closure:     to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::MPZ:         to_mpz_core(it)->dealloc(); break;
            case vm_obj_kind::External:    delete to_external(it); break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

vm_instr mk_push_instr(unsigned idx) {
    vm_instr r(opcode::Push);
    r.m_idx = idx;
    return r;
};

vm_instr mk_drop_instr(unsigned n) {
    vm_instr r(opcode::Drop);
    r.m_num = n;
    return r;
}

vm_instr mk_goto_instr(unsigned pc) {
    vm_instr r(opcode::Goto);
    r.m_pc = pc;
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
    vm_instr r(opcode::Num);
    r.m_mpz = new mpz(v);
    return r;
}

vm_instr mk_ret_instr() { return vm_instr(opcode::Ret); }

vm_instr mk_cases1_instr() { return vm_instr(opcode::Cases1); }

vm_instr mk_nat_cases_instr(unsigned pc) {
    vm_instr r(opcode::NatCases);
    r.m_pc = pc;
    return r;
}

vm_instr mk_cases2_instr(unsigned pc) {
    vm_instr r(opcode::Cases2);
    r.m_pc = pc;
    return r;
}

vm_instr mk_casesn_instr(unsigned num_pc, unsigned const * pcs) {
    lean_assert(num_pc >= 2);
    vm_instr r(opcode::CasesN);
    r.m_npcs = new unsigned[num_pc + 1];
    r.m_npcs[0] = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_invoke_instr(unsigned n) {
    vm_instr r(opcode::Invoke);
    r.m_num = n;
    return r;
}

vm_instr mk_invoke_global_instr(unsigned fn_idx, unsigned n) {
    vm_instr r(opcode::InvokeGlobal);
    r.m_fn_idx = fn_idx;
    r.m_nargs  = n;
    return r;
}

vm_instr mk_closure_instr(unsigned fn_idx, unsigned n) {
    vm_instr r(opcode::Closure);
    r.m_fn_idx = fn_idx;
    r.m_nargs  = n;
    return r;
}

void vm_instr::copy_args(vm_instr const & i) {
    switch (i.m_op) {
    case opcode::InvokeGlobal: case opcode::Closure:
        m_fn_idx = i.m_fn_idx;
        m_nargs  = i.m_nargs;
        break;
    case opcode::Push:
        m_idx  = i.m_idx;
        break;
    case opcode::Invoke: case opcode::Drop:
        m_num = i.m_num;
        break;
    case opcode::Goto: case opcode::Cases2: case opcode::NatCases:
        m_pc = i.m_pc;
        break;
    case opcode::CasesN:
        m_npcs = new unsigned[i.m_npcs[0] + 1];
        for (unsigned j = 0; j < m_npcs[0] + 1; j++)
            m_npcs[j] = i.m_npcs[j];
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
    case opcode::Ret: case opcode::Cases1:
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
    case opcode::CasesN:
        m_npcs   = i.m_npcs;
        i.m_npcs = nullptr;
        break;
    default:
        copy_args(i);
        break;
    }
}

vm_instr::~vm_instr() {
    switch (m_op) {
    case opcode::Num:
        delete m_mpz;
        break;
    case opcode::CasesN:
        delete[] m_npcs;
        break;
    default:
        break;
    }
}

vm_instr & vm_instr::operator=(vm_instr const & s) {
    m_op = s.m_op;
    copy_args(s);
    return *this;
}

vm_instr & vm_instr::operator=(vm_instr && s) {
    m_op = s.m_op;
    switch (m_op) {
    case opcode::Num:
        m_mpz    = s.m_mpz;
        s.m_mpz  = nullptr;
        break;
    case opcode::CasesN:
        m_npcs   = s.m_npcs;
        s.m_npcs = nullptr;
        break;
    default:
        copy_args(s);
        break;
    }
    return *this;
}
}
