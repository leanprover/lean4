/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/interrupt.h"
#include "util/sstream.h"
#include "util/parray.h"
#include "util/small_object_allocator.h"
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

MK_THREAD_LOCAL_GET(small_object_allocator, get_small_allocator, "vm object");

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
    return mk_vm_composite(vm_obj_kind::Constructor, cidx, sz, data);
}

vm_obj mk_vm_closure(unsigned fn_idx, unsigned sz, vm_obj const * data) {
    return mk_vm_composite(vm_obj_kind::Closure, fn_idx, sz, data);
}

vm_mpz::vm_mpz(mpz const & v):
    vm_obj_cell(vm_obj_kind::MPZ),
    m_value(v) {
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

void display(std::ostream & out, vm_obj const & o, std::function<optional<name>(unsigned)> const & idx2name) {
    if (is_simple(o)) {
        out << cidx(o);
    } else if (is_constructor(o)) {
        out << "(#" << cidx(o);
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i), idx2name);
        }
        out << ")";
    } else if (is_mpz(o)) {
        out << to_mpz(o);
    } else if (is_external(o)) {
        out << "[external]";
    } else if (is_closure(o)) {
        if (auto n = idx2name(cfn_idx(o))) {
            out << "(" << *n;
        } else {
            out << "(fn#" << cfn_idx(o);
        }
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i), idx2name);
        }
        out << ")";
    } else {
        out << "[unknown]";
    }
}

void display(std::ostream & out, vm_obj const & o) {
    display(out, o, [](unsigned) { return optional<name>(); });
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
    case opcode::Goto:          out << "goto " << m_pc[0]; break;
    case opcode::SConstructor:  out << "scnstr " << m_cidx; break;
    case opcode::Constructor:   out << "cnstr " << m_cidx << " " << m_nfields; break;
    case opcode::Num:           out << "num " << *m_mpz; break;
    case opcode::Unreachable:   out << "unreachable"; break;
    case opcode::Destruct:      out << "destruct"; break;
    case opcode::Cases2:        out << "cases2 " << m_pc[0] << " " << m_pc[1]; break;
    case opcode::CasesN:
        out << "cases";
        for (unsigned i = 0; i < get_casesn_size(); i++)
            out << " " << get_casesn_pc(i);
        break;
    case opcode::NatCases:      out << "nat_cases " << m_pc[0] << " " << m_pc[1]; break;
    case opcode::Proj:          out << "proj " << m_idx; break;
    case opcode::Invoke:        out << "invoke " << m_nargs; break;
    case opcode::InvokeGlobal:
        out << "ginvoke ";
        display_fn(out, idx2name, m_fn_idx);
        break;
    case opcode::InvokeBuiltin:
        out << "builtin ";
        display_fn(out, idx2name, m_fn_idx);
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

unsigned vm_instr::get_num_pcs() const {
    switch (m_op) {
    case opcode::Goto:
        return 1;
    case opcode::Cases2: case opcode::NatCases:
        return 2;
    case opcode::CasesN:
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
    case opcode::CasesN:
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
    case opcode::CasesN:
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

vm_instr mk_ret_instr() { return vm_instr(opcode::Ret); }

vm_instr mk_destruct_instr() { return vm_instr(opcode::Destruct); }

vm_instr mk_unreachable_instr() { return vm_instr(opcode::Unreachable); }

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
    r.m_npcs = new unsigned[num_pc + 1];
    r.m_npcs[0] = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_invoke_instr(unsigned n) {
    vm_instr r(opcode::Invoke);
    r.m_nargs = n;
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

vm_instr mk_closure_instr(unsigned fn_idx, unsigned n) {
    vm_instr r(opcode::Closure);
    r.m_fn_idx = fn_idx;
    r.m_nargs  = n;
    return r;
}

void vm_instr::copy_args(vm_instr const & i) {
    switch (i.m_op) {
    case opcode::InvokeGlobal: case opcode::InvokeBuiltin:
        m_fn_idx = i.m_fn_idx;
        break;
    case opcode::Closure:
        m_fn_idx = i.m_fn_idx;
        m_nargs  = i.m_nargs;
        break;
    case opcode::Push: case opcode::Proj:
        m_idx  = i.m_idx;
        break;
    case opcode::Invoke:
        m_nargs  = i.m_nargs;
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
    case opcode::Ret: case opcode::Destruct: case opcode::Unreachable:
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

void vm_state::push_fields(vm_obj const & obj) {
    if (is_constructor(obj)) {
        unsigned nflds = csize(obj);
        vm_obj const * flds = cfields(obj);
        for (unsigned i = 0; i < nflds; i++, flds++) {
            m_stack.push_back(*flds);
        }
    }
}

void vm_state::invoke_builtin(vm_decl const & d) {
    unsigned saved_bp = m_bp;
    unsigned sz = m_stack.size();
    m_bp = sz;
    d.get_fn()(*this);
    lean_assert(m_stack.size() == sz + 1);
    m_bp = saved_bp;
    sz = m_stack.size();
    swap(m_stack[sz - d.get_arity() - 1], m_stack[sz - 1]);
    m_stack.resize(sz - d.get_arity());
    m_pc++;
}

void vm_state::invoke_global(vm_decl const & d) {
    m_call_stack.emplace_back(m_code, m_fn_idx, d.get_arity(), m_pc+1, m_bp);
    m_code            = d.get_code();
    m_fn_idx          = d.get_idx();
    m_pc              = 0;
    m_bp              = m_stack.size() - d.get_arity();
}

void vm_state::display_stack(std::ostream & out) const {
    for (unsigned i = 0; i < m_stack.size(); i++) {
        if (i == m_bp)
            out << "[bp] ";
        else
            out << "     ";
        display(out, m_stack[i]);
        out << "\n";
    }
    if (m_bp == m_stack.size())
        out << "[bp]\n";
}

void vm_state::run() {
    lean_assert(m_code);
    unsigned init_call_stack_sz = m_call_stack.size();
    m_pc = 0;
    while (true) {
      main_loop:
        vm_instr const & instr = m_code[m_pc];
        DEBUG_CODE({
                /* We only trace VM in debug mode */
                lean_trace(name({"vm", "run"}),
                           tout() << m_pc << ": ";
                           instr.display(tout().get_stream(), [&](unsigned idx) {
                                   return optional<name>(m_decls[idx].get_name());
                               });
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
            lean_assert(sz > num);
            swap(m_stack[sz - num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - num);
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
            vm_obj new_value = mk_vm_constructor(instr.get_cidx(), nfields, m_stack.data() + sz - nfields);
            m_stack.resize(sz - nfields + 1);
            swap(m_stack.back(), new_value);
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
            vm_obj new_value   = mk_vm_closure(instr.get_fn_idx(), nargs, m_stack.data() + sz - nargs);
            m_stack.resize(sz - nargs + 1);
            swap(m_stack.back(), new_value);
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
            m_stack.pop_back();
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
            m_stack.pop_back();
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
                    m_stack.pop_back();
                    m_pc++;
                    goto main_loop;
                } else {
                    vm_obj new_value = mk_vm_simple(val - 1);
                    swap(top, new_value);
                    m_pc = instr.get_cases2_pc(1);
                    goto main_loop;
                }
            } else {
                mpz const & val = to_mpz(top);
                if (val == 0) {
                    m_stack.pop_back();
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
            m_stack.pop_back();
            push_fields(top);
            m_pc = instr.get_casesn_pc(cidx(top));
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
        case opcode::Ret: {
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
            frame const & fr = m_call_stack.back();
            unsigned sz      = m_stack.size();
            swap(m_stack[sz - fr.m_num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - fr.m_num);
            m_code   = fr.m_code;
            m_fn_idx = fr.m_fn_idx;
            m_pc     = fr.m_pc;
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
            /**
               Instruction: invoke n

               Case 1) n + m < fn.arity, where m is the number of arguments in the closure,
               and fn is the function stored in the closure.

               stack before                    after
               ...                             ...
               v                               v
               a_n                             (closure fn a_n ... a_1 b_m ... b_1)
               ...                       ==>
               a_1
               (closure fn b_m ... b_1)

               Case 2) n + m == fn.arity and fn is not builtin.
               See InvokeGlobal case.

               Case 3) n + m == fn.arity and fn is builtin.
               See InvokeBuiltin case.
            */
            unsigned nargs    = instr.get_nargs();
            unsigned sz       = m_stack.size();
            vm_obj closure    = m_stack.back();
            m_stack.pop_back();
            unsigned fn_idx   = cfn_idx(closure);
            vm_decl const & d = m_decls[fn_idx];
            unsigned csz      = csize(closure);
            unsigned arity    = d.get_arity();
            unsigned new_nargs = nargs + csz;
            lean_assert(new_nargs <= arity);
            std::copy(cfields(closure), cfields(closure) + csz, std::back_inserter(m_stack));
            /* Now, stack contains closure arguments + original stack arguments */
            if (new_nargs == arity) {
                if (d.is_builtin())
                    invoke_builtin(d);
                else
                    invoke_global(d);
                goto main_loop;
            } else {
                /* We don't have sufficient arguments. So, we create a new closure */
                sz = m_stack.size();
                vm_obj new_value = mk_vm_closure(fn_idx, new_nargs, m_stack.data() + sz - new_nargs);
                m_stack.resize(sz - new_nargs + 1);
                swap(m_stack.back(), new_value);
                m_pc++;
                goto main_loop;
            }
        }
        case opcode::InvokeGlobal:
            check_interrupted();
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
            invoke_global(m_decls[instr.get_fn_idx()]);
            goto main_loop;
        case opcode::InvokeBuiltin:
            check_interrupted();
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
            invoke_builtin(m_decls[instr.get_fn_idx()]);
            goto main_loop;
        }
    }
}

void vm_state::invoke_fn(name const & fn) {
    if (auto r = m_fn_name2idx.find(fn)) {
        invoke_fn(*r);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

void vm_state::invoke_fn(unsigned fn_idx) {
    lean_assert(fn_idx < m_decls.size());
    vm_decl const & d = m_decls[fn_idx];
    unsigned arity    = d.get_arity();
    if (arity > m_stack.size())
        throw exception("invalid VM function call, data stack does not have enough values");
    if (d.is_builtin())
        invoke_builtin(d);
    else
        invoke_global(d);
    run();
}

void vm_state::display(std::ostream & out, vm_obj const & o) const {
    ::lean::display(out, o, [&](unsigned idx) { return optional<name>(m_decls[idx].get_name()); });
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
    DEBUG_CODE({
            /* We only trace VM in debug mode because it produces a 10% performance penalty */
            register_trace_class("vm");
            register_trace_class({"vm", "run"});
        });
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
