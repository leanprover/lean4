/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/sstream.h"
#include "util/parray.h"
#include "library/constants.h"
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

vm_obj mk_vm_simple(unsigned v) {
    return vm_obj(v);
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

static void display_fn(std::ostream & out, std::function<optional<name>(unsigned)> const & idx2name, unsigned fn_idx) {
    if (auto r = idx2name(fn_idx))
        out << *r;
    else
        out << fn_idx;
}

void vm_instr::display(std::ostream & out, std::function<optional<name>(unsigned)> const & idx2name) const {
    switch (m_op) {
    case opcode::Push:          out << "push " << m_idx; break;
    case opcode::Ret:           out << "ret"; break;
    case opcode::Drop:          out << "drop " << m_num; break;
    case opcode::Goto:          out << "goto " << m_pc; break;
    case opcode::SConstructor:  out << "scnstr " << m_cidx; break;
    case opcode::Constructor:   out << "cnstr " << m_cidx << " " << m_nfields; break;
    case opcode::Num:           out << "num " << *m_mpz; break;
    case opcode::Cases1:        out << "cases1"; break;
    case opcode::Cases2:        out << "cases2 " << m_pc; break;
    case opcode::CasesN:
        out << "cases";
        for (unsigned i = 0; i < get_num_pcs(); i++)
            out << " " << get_pc(i);
        break;
    case opcode::NatCases:      out << "nat_cases " << m_pc; break;
    case opcode::Proj:          out << "proj " << m_idx; break;
    case opcode::Invoke:        out << "invoke " << m_num; break;
    case opcode::InvokeGlobal:
        out << "ginvoke ";
        display_fn(out, idx2name, m_fn_idx);
        out << " " << m_nargs;
        break;
    case opcode::Closure:
        out << "closure ";
        display_fn(out, idx2name, m_fn_idx);
        out << " " << m_nargs;
        break;
    }
}

void vm_instr::display(std::ostream & out) const {
    display(out, [](unsigned) { return optional<name>(); });
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

vm_instr mk_proj_instr(unsigned n) {
    vm_instr r(opcode::Proj);
    r.m_idx = n;
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
    case opcode::Invoke: case opcode::Drop: case opcode::Proj:
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


vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_function fn):
    m_rc(0), m_builtin(true), m_name(n), m_idx(idx), m_arity(arity), m_fn(fn) {}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, expr const & e, unsigned code_sz, vm_instr const * code):
    m_rc(0), m_builtin(false), m_name(n), m_idx(idx), m_expr(e), m_arity(0),
    m_code_size(code_sz) {
    expr it = e;
    while (is_lambda(it)) {
        m_arity++;
        it = binding_body(it);
    }
    m_code = new vm_instr[code_sz];
    for (unsigned i = 0; i < code_sz; i++)
        m_code[i] = code[i];
}

vm_decl_cell::~vm_decl_cell() {
    if (!m_builtin)
        delete[] m_code;
}

void vm_decl_cell::dealloc() {
    delete this;
}

/** \brief VM builtin functions */
static name_map<pair<unsigned, vm_function>> * g_vm_builtins = nullptr;

void declare_vm_builtin(name const & n, unsigned arity, vm_function fn) {
    g_vm_builtins->insert(n, mk_pair(arity, fn));
}

bool is_vm_builtin_function(name const & fn) {
    return g_vm_builtins->contains(fn);
}

/** \brief VM function/constant declarations are stored in an environment extension. */
struct vm_decls : public environment_extension {
    bool               m_initialized;
    name_map<unsigned> m_name2idx;
    parray<vm_decl>    m_decls;
    vm_decls():m_initialized(false) {}

    void add(vm_decl const & d) {
        if (m_name2idx.contains(d.get_name()))
            throw exception(sstream() << "VM already contains code for '" << d.get_name() << "'");
        m_name2idx.insert(d.get_name(), d.get_idx());
        m_decls.push_back(d);
    }

    unsigned reserve(name const & n, expr const & e) {
        if (m_name2idx.contains(n))
            throw exception(sstream() << "VM already contains code for '" << n << "'");
        unsigned idx = m_decls.size();
        m_name2idx.insert(n, idx);
        m_decls.push_back(vm_decl(n, idx, e, 0, nullptr));
        return idx;
    }

    void update(name const & n, unsigned code_sz, vm_instr const * code) {
        lean_assert(m_name2idx.contains(n));
        unsigned idx = *m_name2idx.find(n);
        vm_decl d    = m_decls[idx];
        m_decls.set(idx, vm_decl(n, idx, d.get_expr(), code_sz, code));
    }

    void initialize() {
        if (!m_initialized) {
            m_initialized = true;
            g_vm_builtins->for_each([&](name const & n, pair<unsigned, vm_function> const & p) {
                    add(vm_decl(n, m_decls.size(), p.first, p.second));
                });
        }
    }
};

struct vm_decls_reg {
    unsigned m_ext_id;
    vm_decls_reg() { m_ext_id = environment::register_extension(std::make_shared<vm_decls>()); }
};

static vm_decls_reg * g_ext = nullptr;
static vm_decls const & get_extension(environment const & env) {
    return static_cast<vm_decls const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, vm_decls const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<vm_decls>(ext));
}

environment initialize_vm_builtin_decls(environment const & env) {
    auto ext = get_extension(env);
    if (ext.m_initialized)
        return env;
    ext.initialize();
    return update(env, ext);
}

bool is_vm_function(environment const & env, name const & fn) {
    auto const & ext = get_extension(env);
    return ext.m_name2idx.contains(fn) || g_vm_builtins->contains(fn);
}

optional<unsigned> get_vm_constant_idx(environment const & env, name const & n) {
    auto const & ext = get_extension(env);
    if (auto r = ext.m_name2idx.find(n))
        return optional<unsigned>(*r);
    else
        return optional<unsigned>();
}

environment reserve_vm_index(environment const & env, name const & fn, expr const & e) {
    vm_decls ext = get_extension(env);
    ext.initialize();
    ext.reserve(fn, e);
    return update(env, ext);
}

environment update_vm_code(environment const & env, name const & fn, unsigned code_sz, vm_instr const * code) {
    vm_decls ext = get_extension(env);
    ext.initialize();
    ext.update(fn, code_sz, code);
    // TODO(Leo): store bytecode in .olean file
    return update(env, ext);
}

environment add_vm_code(environment const & env, name const & fn, expr const & e, unsigned code_sz, vm_instr const * code) {
    environment new_env = reserve_vm_index(env, fn, e);
    return update_vm_code(new_env, fn, code_sz, code);
}

environment optimize_vm_decls(environment const & env) {
    vm_decls ext = get_extension(env);
    if (ext.m_decls.is_compressed()) {
        return env;
    } else {
        ext.m_decls.compress();
        return update(env, ext);
    }
}

optional<vm_decl> get_vm_decl(environment const & env, name const & n) {
    vm_decls const & ext = get_extension(env);
    if (auto idx = ext.m_name2idx.find(n))
        return optional<vm_decl>(ext.m_decls[*idx]);
    else
        return optional<vm_decl>();
}

vm_state::vm_state(environment const & env):
    m_env(optimize_vm_decls(env)),
    m_decls(get_extension(m_env).m_decls.as_vector_if_compressed()),
    m_code(nullptr),
    m_fn_idx(0),
    m_pc(0),
    m_bp(0) {
}

void display_vm_code(std::ostream & out, environment const & env, unsigned code_sz, vm_instr const * code) {
    vm_decls const & ext = get_extension(env);
    auto idx2name = [&](unsigned idx) {
        if (idx < ext.m_decls.size()) {
            return optional<name>(ext.m_decls[idx].get_name());
        } else {
            return optional<name>();
        }
    };

    for (unsigned i = 0; i < code_sz; i++) {
        out << i << ": ";
        code[i].display(out, idx2name);
        out << "\n";
    }
}

// =======================================
// Builtin nat operations
#define MAX_SMALL_NAT 1u<<31

vm_obj mk_vm_nat(unsigned n) {
    if (n < MAX_SMALL_NAT)
        return mk_vm_simple(n);
    else
        return mk_vm_mpz(mpz(n));
}

vm_obj mk_vm_nat(mpz const & n) {
    if (n < MAX_SMALL_NAT)
        return mk_vm_simple(n.get_unsigned_int());
    else
        return mk_vm_mpz(n);
}

MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz1);
MK_THREAD_LOCAL_GET_DEF(mpz, get_mpz2);

static mpz const & to_mpz1(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz1();
        r = cidx(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

static mpz const & to_mpz2(vm_obj const & o) {
    if (is_simple(o)) {
        mpz & r = get_mpz2();
        r = cidx(o);
        return r;
    } else {
        return to_mpz(o);
    }
}

static void nat_succ(vm_state & s) {
    vm_obj const & a = s.get(0);
    if (is_simple(a)) {
        s.push(mk_vm_nat(cidx(a) + 1));
    } else {
        s.push(mk_vm_mpz(to_mpz1(a) + 1));
    }
}

static void nat_add(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        s.push(mk_vm_nat(cidx(a1) + cidx(a2)));
    } else {
        s.push(mk_vm_mpz(to_mpz1(a1) + to_mpz2(a2)));
    }
}

static void nat_mul(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned long long r = static_cast<unsigned long long>(cidx(a1)) + static_cast<unsigned long long>(cidx(a2));
        if (r < MAX_SMALL_NAT) {
            s.push(mk_vm_simple(r));
            return;
        }
    }
    s.push(mk_vm_mpz(to_mpz1(a1) * to_mpz2(a2)));
}

static void nat_sub(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 > v1)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 - v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 > v1)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 - v2));
    }
}

static void nat_div(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 / v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            s.push(mk_vm_simple(0));
        else
            s.push(mk_vm_nat(v1 / v2));
    }
}

static void nat_mod(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        unsigned v1 = cidx(a1);
        unsigned v2 = cidx(a2);
        if (v2 == 0)
            s.push(a1);
        else
            s.push(mk_vm_nat(v1 % v2));
    } else {
        mpz const & v1 = to_mpz1(a1);
        mpz const & v2 = to_mpz2(a2);
        if (v2 == 0)
            s.push(a1);
        else
            s.push(mk_vm_nat(v1 % v2));
    }
}

static void nat_gcd(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    mpz r;
    gcd(r, to_mpz1(a1), to_mpz2(a2));
    s.push(mk_vm_nat(r));
}

static void nat_has_decidable_eq(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        return s.push(mk_vm_bool(cidx(a1) == cidx(a2)));
    } else {
        return s.push(mk_vm_bool(to_mpz1(a1) == to_mpz2(a2)));
    }
}

static void nat_has_decidable_le(vm_state & s) {
    vm_obj const & a1 = s.get(0);
    vm_obj const & a2 = s.get(1);
    if (is_simple(a1) && is_simple(a2)) {
        return s.push(mk_vm_bool(cidx(a1) <= cidx(a2)));
    } else {
        return s.push(mk_vm_bool(to_mpz1(a1) <= to_mpz2(a2)));
    }
}

void initialize_vm() {
    g_vm_builtins = new name_map<pair<unsigned, vm_function>>();
    declare_vm_builtin(get_nat_succ_name(),              1, nat_succ);
    declare_vm_builtin(get_nat_add_name(),               2, nat_add);
    declare_vm_builtin(get_nat_mul_name(),               2, nat_mul);
    declare_vm_builtin(get_nat_sub_name(),               2, nat_sub);
    declare_vm_builtin(get_nat_div_name(),               2, nat_div);
    declare_vm_builtin(get_nat_mod_name(),               2, nat_mod);
    declare_vm_builtin(get_nat_gcd_name(),               2, nat_gcd);
    declare_vm_builtin(get_nat_has_decidable_eq_name(),  2, nat_has_decidable_eq);
    declare_vm_builtin(get_nat_has_decidable_le_name(),  2, nat_has_decidable_le);
    g_ext = new vm_decls_reg();
}

void finalize_vm() {
    delete g_ext;
    delete g_vm_builtins;
}
}
