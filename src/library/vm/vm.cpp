/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/sstream.h"
#include "util/parray.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/vm/vm.h"

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

void display(std::ostream & out, vm_obj const & o) {
    if (is_simple(o)) {
        out << cidx(o);
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
        out << "[closure]";
    } else {
        out << "[unknown]";
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
    case opcode::Unreachable:   out << "unreachable"; break;
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

vm_instr mk_ret_instr() { return vm_instr(opcode::Ret); }

vm_instr mk_cases1_instr() { return vm_instr(opcode::Cases1); }

vm_instr mk_unreachable_instr() { return vm_instr(opcode::Unreachable); }

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
    case opcode::Push: case opcode::Proj:
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
    case opcode::Ret: case opcode::Cases1: case opcode::Unreachable:
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
    name_map<unsigned> m_name2idx;
    parray<vm_decl>    m_decls;

    vm_decls() {
        g_vm_builtins->for_each([&](name const & n, pair<unsigned, vm_function> const & p) {
                add(vm_decl(n, m_decls.size(), p.first, p.second));
            });
    }

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
    ext.reserve(fn, e);
    return update(env, ext);
}

environment update_vm_code(environment const & env, name const & fn, unsigned code_sz, vm_instr const * code) {
    vm_decls ext = get_extension(env);
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
    m_fn_name2idx(get_extension(m_env).m_name2idx),
    m_code(nullptr),
    m_fn_idx(0),
    m_bp(0) {
}

#define PushFields(obj)                                 \
if (is_constructor(obj)) {                              \
    unsigned nflds = csize(obj);                        \
    vm_obj const * flds = cfields(obj);                 \
    for (unsigned i = 0; i < nflds; i++, flds++) {      \
        m_stack.push_back(*flds);                       \
    }                                                   \
}

#define InvokeGlobal(d)                                                 \
if (d.is_builtin()) {                                                   \
    unsigned saved_bp = m_bp;                                           \
    unsigned sz = m_stack.size();                                       \
    m_bp = sz - d.get_arity();                                          \
    d.get_fn()(*this);                                                  \
    lean_assert(m_stack.size() == sz + 1);                              \
    m_bp = saved_bp;                                                    \
    sz = m_stack.size();                                                \
    std::swap(m_stack[sz - d.get_arity() - 1], m_stack[sz - 1]);        \
    m_stack.resize(sz - d.get_arity());                                 \
    pc++;                                                               \
} else {                                                                \
    m_call_stack.emplace_back(m_code, m_fn_idx, d.get_arity(), pc+1, m_bp); \
    m_code            = d.get_code();                                   \
    m_fn_idx          = d.get_idx();                                    \
    pc                = 0;                                              \
    m_bp              = m_stack.size() - d.get_arity();                 \
}

void vm_state::run() {
    /*
       TODO(Leo): we can improve performance using the following tricks:
       - Function arguments in reverse order.
       - Function pointer after arguments.
       - For Cases2, NatCases and CasesN store the pc for cidx 0 case.
       - We don't need to store nargs at InvokeGlobal
    */
    lean_assert(m_code);
    unsigned init_call_stack_sz = m_call_stack.size();
    unsigned pc  = 0;
    while (true) {
      main_loop:
        vm_instr const & instr = m_code[pc];
        lean_trace(name({"vm", "run"}),
                   tout() << pc << ": ";
                   instr.display(tout().get_stream(), [&](unsigned idx) { return optional<name>(m_decls[idx].get_name()); });
                   tout() << ", bp: " << m_bp << "\n";
                   for (unsigned i = 0; i < m_stack.size(); i++) {
                       tout() << i << " := ";
                       display(tout().get_stream(), m_stack[i]);
                       tout() << "\n";
                   }
                   tout() << "\n";);
        switch (instr.op()) {
        case opcode::Push:
            m_stack.push_back(m_stack[m_bp + instr.get_idx()]);
            pc++;
            goto main_loop;
        case opcode::Drop: {
            unsigned num = instr.get_num();
            unsigned sz  = m_stack.size();
            lean_assert(sz > num);
            std::swap(m_stack[sz - num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - num);
            pc++;
            goto main_loop;
        }
        case opcode::Goto:
            pc = instr.get_pc();
            goto main_loop;
        case opcode::SConstructor:
            m_stack.push_back(mk_vm_simple(instr.get_cidx()));
            pc++;
            goto main_loop;
        case opcode::Constructor: {
            unsigned nfields = instr.get_nfields();
            unsigned sz      = m_stack.size();
            vm_obj new_value = mk_vm_constructor(instr.get_cidx(), nfields, m_stack.data() + sz - nfields);
            m_stack.resize(sz - nfields);
            m_stack.push_back(new_value);
            pc++;
            goto main_loop;
        }
        case opcode::Closure: {
            unsigned nargs     = instr.get_nargs();
            unsigned sz        = m_stack.size();
            vm_obj new_value   = mk_vm_closure(instr.get_fn_idx(), nargs, m_stack.data() + sz - nargs);
            m_stack.resize(sz - nargs);
            m_stack.push_back(new_value);
            pc++;
            goto main_loop;
        }
        case opcode::Num:
            m_stack.push_back(mk_vm_mpz(instr.get_mpz()));
            pc++;
            goto main_loop;
        case opcode::Cases1: {
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            PushFields(top);
            pc++;
            goto main_loop;
        }
        case opcode::Cases2: {
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            PushFields(top);
            if (cidx(top) == 0)
                pc++;
            else
                pc = instr.get_pc();
            goto main_loop;
        }
        case opcode::NatCases: {
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            if (is_simple(top)) {
                unsigned val = cidx(top);
                if (val == 0) {
                    pc++;
                    goto main_loop;
                } else {
                    m_stack.push_back(mk_vm_simple(val - 1));
                    pc = instr.get_pc();
                    goto main_loop;
                }
            } else {
                mpz const & val = to_mpz(top);
                if (val == 0) {
                    pc++;
                    goto main_loop;
                } else {
                    m_stack.push_back(mk_vm_mpz(val - 1));
                    pc = instr.get_pc();
                    goto main_loop;
                }
            }
        }
        case opcode::CasesN: {
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            PushFields(top);
            if (cidx(top) == 0)
                pc++;
            else
                pc = instr.get_pc(cidx(top) - 1);
            goto main_loop;
        }
        case opcode::Proj: {
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            m_stack.push_back(cfield(top, instr.get_idx()));
            pc++;
            goto main_loop;
        }
        case opcode::Unreachable:
            throw exception("VM unreachable instruction has been reached");
        case opcode::Ret: {
            frame const & fr = m_call_stack.back();
            unsigned sz      = m_stack.size();
            std::swap(m_stack[sz - fr.m_num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - fr.m_num);
            m_code   = fr.m_code;
            m_fn_idx = fr.m_fn_idx;
            pc       = fr.m_pc;
            m_bp     = fr.m_bp;
            if (m_call_stack.size() == init_call_stack_sz) {
                m_call_stack.pop_back();
                return;
            } else {
                m_call_stack.pop_back();
                goto main_loop;
            }
        }
        case opcode::Invoke: {
            unsigned nargs    = instr.get_nargs();
            unsigned sz       = m_stack.size();
            vm_obj closure    = m_stack[sz - nargs - 1];
            unsigned fn_idx   = cfn_idx(closure);
            vm_decl const & d = m_decls[fn_idx];
            unsigned csz      = csize(closure);
            unsigned arity    = d.get_arity();
            unsigned new_nargs = nargs + csz;
            lean_assert(new_nargs <= arity);
            if (csz == 0) {
                /* Closure has size 0, then we just move arguments down 1 position */
                m_stack.erase(m_stack.end() - nargs - 1); /* remove closure object */
            } else if (csz == 1) {
                /* Closure has size 1, then we replace the closure object with
                   the data stored in the closure */
                *(m_stack.end() - nargs - 1) = cfield(closure, 0);
            } else {
                lean_assert(csz > 1);
                /* Closure has size > 1, then we need to open space on the stack */
                m_stack.resize(sz + csz - 1);
                std::move_backward(m_stack.end() - nargs + 1 - csz, m_stack.end() + 1 - csz, m_stack.end());
                std::copy(cfields(closure), cfields(closure) + csz, m_stack.end() - nargs - csz);
            }
            /* Now, stack contains closure arguments + original stack arguments */
            if (new_nargs == arity) {
                InvokeGlobal(d);
                goto main_loop;
            } else {
                /* We don't have sufficient arguments. So, we create a new closure */
                sz = m_stack.size();
                vm_obj new_value = mk_vm_closure(fn_idx, new_nargs, m_stack.data() + sz - new_nargs);
                m_stack.resize(sz - new_nargs);
                m_stack.push_back(new_value);
                pc++;
                goto main_loop;
            }
        }
        case opcode::InvokeGlobal: {
            vm_decl const & d = m_decls[instr.get_fn_idx()];
            InvokeGlobal(d);
            goto main_loop;
        }
        }
    }
}

void vm_state::invoke_global(name const & fn) {
    if (auto r = m_fn_name2idx.find(fn)) {
        invoke_global(*r);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

void vm_state::invoke_global(unsigned fn_idx) {
    lean_assert(fn_idx < m_decls.size());
    vm_decl const & d = m_decls[fn_idx];
    unsigned pc       = 0;
    unsigned arity    = d.get_arity();
    if (arity > m_stack.size())
        throw exception("invalid VM function call, data stack does not have enough values");
    InvokeGlobal(d);
    run();
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

void initialize_vm_core() {
    g_vm_builtins = new name_map<pair<unsigned, vm_function>>();
    register_trace_class("vm");
    register_trace_class({"vm", "run"});
}

void finalize_vm_core() {
    delete g_vm_builtins;
}

void initialize_vm() {
    g_ext = new vm_decls_reg();
}

void finalize_vm() {
    delete g_ext;
}
}
