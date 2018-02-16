/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <algorithm>
#include <vector>
#include <string>
#include <cstdint>
#include "util/debug.h"
#include "util/compiler_hints.h"
#include "util/rc.h"
#include "util/interrupt.h"
#include "util/small_object_allocator.h"
#include "util/serializer.h"
#include "util/numerics/mpz.h"
#include "kernel/environment.h"
#include "kernel/pos_info_provider.h"

namespace lean {
class vm_obj;
class ts_vm_obj;
enum class vm_obj_kind { Simple, Constructor, Closure, NativeClosure, MPZ, External };

/** \brief Base class for VM objects.

    \remark Simple objects are encoded as tagged pointers. */
class vm_obj_cell {
protected:
    friend class vm_obj;
    unsigned    m_rc;
    const vm_obj_kind m_kind;
    void inc_ref() { m_rc++; }
    bool dec_ref_core() {
        lean_assert(m_rc > 0);
        m_rc--;
        return m_rc == 0;
    }
    void dec_ref() { if (dec_ref_core()) { dealloc(); } }
    void dealloc();
    void dec_ref(vm_obj & o, buffer<vm_obj_cell*> & todelete);
    vm_obj_cell(vm_obj_kind k):m_rc(0), m_kind(k) {}
public:
    vm_obj_kind kind() const { return m_kind; }
    unsigned get_rc() const { return m_rc; }
};

#define LEAN_VM_IS_PTR(obj) ((reinterpret_cast<size_t>(obj) & 1) == 0)
#define LEAN_VM_BOX(num)    (reinterpret_cast<vm_obj_cell*>(static_cast<uintptr_t>((num << 1) | 1)))
#define LEAN_VM_UNBOX(obj)  (reinterpret_cast<size_t>(obj) >> 1)

[[noreturn]] void vm_check_failed(char const * condition);
#if defined(LEAN_VM_UNCHECKED)
#define lean_vm_check(cond) lean_assert(cond)
#else
#define lean_vm_check(cond) { if (LEAN_UNLIKELY(!(cond))) vm_check_failed(#cond); }
#endif

void display(std::ostream & out, vm_obj const & o);

/** \brief VM object */
class vm_obj {
    vm_obj_cell * m_data;
    friend class vm_obj_cell;
    friend class ts_vm_obj;
public:
    vm_obj():m_data(LEAN_VM_BOX(0)) {
        static_assert(sizeof(vm_obj) == sizeof(void *), "unexpected class obj size"); // NOLINT
    }
    explicit vm_obj(unsigned cidx):m_data(LEAN_VM_BOX(cidx)) {}
    explicit vm_obj(vm_obj_cell * c):m_data(c) { m_data->inc_ref(); lean_assert(is_ptr()); }
    vm_obj(vm_obj const & o):m_data(o.m_data) { if (is_ptr()) m_data->inc_ref(); }
    vm_obj(vm_obj && o):m_data(o.m_data) { o.m_data = LEAN_VM_BOX(0); }
    ~vm_obj() { if (is_ptr()) m_data->dec_ref(); }

    friend void swap(vm_obj & a, vm_obj & b) { std::swap(a.m_data, b.m_data); }

    operator vm_obj_cell*() const { return m_data; }

    vm_obj & operator=(vm_obj const & s) {
        if (s.is_ptr())
            s.m_data->inc_ref();
        vm_obj_cell * new_data = s.m_data;
        if (is_ptr())
            m_data->dec_ref();
        m_data = new_data;
        return *this;
    }

    vm_obj & operator=(vm_obj && s) {
        if (is_ptr())
            m_data->dec_ref();
        m_data   = s.m_data;
        s.m_data = LEAN_VM_BOX(0);
        return *this;
    }

    inline bool is_ptr() const {
        return LEAN_VM_IS_PTR(m_data);
    }

    vm_obj_kind kind() const {
        return is_ptr() ? m_data->kind() : vm_obj_kind::Simple;
    }

    vm_obj_cell * raw() const {
        return m_data;
    }

    vm_obj_cell * steal_ptr() {
        lean_assert(is_ptr()); vm_obj_cell * r = m_data; m_data = LEAN_VM_BOX(0); return r;
    }
};

class vm_composite : public vm_obj_cell {
    unsigned   m_idx;
    unsigned   m_size;
    vm_obj * get_field_ptr() {
        return reinterpret_cast<vm_obj *>(reinterpret_cast<char *>(this)+sizeof(vm_composite));
    }
    friend vm_obj_cell;
    void dealloc(buffer<vm_obj_cell*> & todelete);
public:
    vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data);
    unsigned size() const { return m_size; }
    unsigned idx() const { return m_idx; }
    vm_obj const * fields() const {
        return reinterpret_cast<vm_obj const *>(reinterpret_cast<char const *>(this)+sizeof(vm_composite));
    }
};

class vm_mpz : public vm_obj_cell {
    mpz      m_value;
    friend vm_obj_cell;
    void dealloc();
public:
    vm_mpz(mpz const & v);
    mpz const & get_value() const { return m_value; }
};

typedef std::function<vm_obj(vm_obj const &)> vm_clone_fn;

class vm_external : public vm_obj_cell {
protected:
    friend vm_obj_cell;
    virtual void dealloc() = 0;
public:
    vm_external():vm_obj_cell(vm_obj_kind::External) {}
    virtual ~vm_external() {}
    virtual vm_external * ts_clone(vm_clone_fn const &) = 0;
    virtual vm_external * clone(vm_clone_fn const &) = 0;
};

/* Thread safe vm_obj, it can be used to move vm_obj's between threads.
   We perform a deep copy to convert a vm_obj into a ts_vm_obj, and vice-versa. */
class ts_vm_obj {
    struct to_ts_vm_obj_fn;
    struct to_vm_obj_fn;
    struct data {
        vm_obj                     m_root;
        std::vector<vm_obj_cell *> m_objs;
        ~data();
    };
    static void steal_ptr(vm_obj & o) { o.steal_ptr(); }
    std::shared_ptr<data>          m_data;
public:
    ts_vm_obj() = default;
    ts_vm_obj(vm_obj const & o);
    vm_obj to_vm_obj() const;
};

/** Builtin functions that take arguments from the system stack.

    \remark The C++ code generator produces this kind of function. */
typedef vm_obj (*vm_cfunction)(vm_obj const &);
typedef vm_obj (*vm_cfunction_0)();
typedef vm_obj (*vm_cfunction_1)(vm_obj const &);
typedef vm_obj (*vm_cfunction_2)(vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_3)(vm_obj const &, vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_4)(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_5)(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &,
                                 vm_obj const &);
typedef vm_obj (*vm_cfunction_6)(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &,
                                 vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_7)(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &,
                                 vm_obj const &, vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_8)(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &,
                                 vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &);
typedef vm_obj (*vm_cfunction_N)(unsigned n, vm_obj const *);

/* Closure for C++ generated code, they do not require a vm_state object to be used. */
class vm_native_closure : public vm_obj_cell {
    vm_cfunction m_fn;
    unsigned     m_arity;
    unsigned     m_num_args;
    vm_obj * get_args_ptr() {
        return reinterpret_cast<vm_obj *>(reinterpret_cast<char *>(this)+sizeof(vm_native_closure));
    }
    friend vm_obj_cell;
    void dealloc(buffer<vm_obj_cell*> & todelete);
public:
    vm_native_closure(vm_cfunction fn, unsigned arity, unsigned num_args, vm_obj const * args);
    vm_cfunction get_fn() const { return m_fn; }
    unsigned get_arity() const { return m_arity; }
    unsigned get_num_args() const { return m_num_args; }
    vm_obj const * get_args() const {
        return reinterpret_cast<vm_obj const *>(reinterpret_cast<char const *>(this)+sizeof(vm_native_closure));
    }
};

small_object_allocator & get_vm_allocator();

// =======================================
// Constructors
vm_obj mk_vm_simple(unsigned cidx);
vm_obj mk_vm_constructor(unsigned cidx, unsigned sz, vm_obj const * args);
vm_obj mk_vm_constructor(unsigned cidx, std::initializer_list<vm_obj const> args);
vm_obj mk_vm_constructor(unsigned cidx, vm_obj const &);
vm_obj mk_vm_constructor(unsigned cidx, vm_obj const &, vm_obj const &);
vm_obj mk_vm_constructor(unsigned cidx, vm_obj const &, vm_obj const &, vm_obj const &);
vm_obj mk_vm_constructor(unsigned cidx, vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &);
vm_obj mk_vm_constructor(unsigned cidx, vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &);
vm_obj update_vm_constructor(vm_obj const & o, unsigned i, vm_obj const & v);
vm_obj update_vm_pair(vm_obj const & o, vm_obj const & v_1, vm_obj const & v_2);
/* TODO(Leo, Jared): delete native closures that take environment as argument */
vm_obj mk_native_closure(environment const & env, name const & n, unsigned sz, vm_obj const * args);
vm_obj mk_native_closure(environment const & env, name const & n, std::initializer_list<vm_obj const> args);
/* Native closures */
vm_obj mk_native_closure(vm_cfunction_1 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_2 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_3 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_4 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_5 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_6 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_7 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_8 fn, unsigned num_args = 0, vm_obj const * args = nullptr);
vm_obj mk_native_closure(vm_cfunction_N fn, unsigned arity, unsigned num_args, vm_obj const * args);
vm_obj mk_native_closure(vm_cfunction_1 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_2 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_3 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_4 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_5 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_6 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_7 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_8 fn, std::initializer_list<vm_obj> const & args);
vm_obj mk_native_closure(vm_cfunction_N fn, unsigned arity, std::initializer_list<vm_obj> const & args);
/* Closure to VM bytecode */
vm_obj mk_vm_closure(unsigned fnidx, unsigned sz, vm_obj const * args);
vm_obj mk_vm_closure(unsigned cidx, vm_obj const &);
vm_obj mk_vm_closure(unsigned cidx, vm_obj const &, vm_obj const &);
vm_obj mk_vm_closure(unsigned cidx, vm_obj const &, vm_obj const &, vm_obj const &);
vm_obj mk_vm_closure(unsigned cidx, vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &);
vm_obj mk_vm_mpz(mpz const & n);
inline vm_obj mk_vm_external(vm_external * obj) { lean_assert(obj && obj->get_rc() == 0); return vm_obj(obj); }
/* helper functions for creating natural numbers */
vm_obj mk_vm_nat(unsigned n);
vm_obj mk_vm_nat(mpz const & n);
inline vm_obj mk_vm_unit() { return mk_vm_simple(0); }
inline vm_obj mk_vm_false() { return mk_vm_simple(0); }
inline vm_obj mk_vm_true() { return mk_vm_simple(1); }
inline vm_obj mk_vm_bool(bool b) { return mk_vm_simple(b); }
inline vm_obj mk_vm_pair(vm_obj const & v1, vm_obj const & v2) { return mk_vm_constructor(0, v1, v2); }
// =======================================

// =======================================
// Testers
inline vm_obj_kind kind(vm_obj_cell const * o) { return LEAN_VM_IS_PTR(o) ? o->kind() : vm_obj_kind::Simple; }
inline bool is_simple(vm_obj_cell const * o) { return !LEAN_VM_IS_PTR(o); }
inline bool is_constructor(vm_obj_cell const * o) { return kind(o) == vm_obj_kind::Constructor; }
inline bool is_closure(vm_obj_cell const * o) { return kind(o) == vm_obj_kind::Closure; }
inline bool is_native_closure(vm_obj_cell const * o) { return kind(o) == vm_obj_kind::NativeClosure; }
inline bool is_composite(vm_obj_cell const * o) { return is_constructor(o) || is_closure(o); }
inline bool is_mpz(vm_obj_cell const * o) { return kind(o) == vm_obj_kind::MPZ; }
inline bool is_external(vm_obj_cell const * o) { return kind(o) == vm_obj_kind::External; }
// =======================================

// =======================================
// Casting
LEAN_ALWAYS_INLINE inline vm_composite * to_composite(vm_obj_cell * o) { lean_vm_check(is_composite(o)); return static_cast<vm_composite*>(o); }
LEAN_ALWAYS_INLINE inline vm_mpz * to_mpz_core(vm_obj_cell * o) { lean_vm_check(is_mpz(o)); return static_cast<vm_mpz*>(o); }
LEAN_ALWAYS_INLINE inline mpz const & to_mpz(vm_obj_cell * o) { return to_mpz_core(o)->get_value(); }
LEAN_ALWAYS_INLINE inline vm_external * to_external(vm_obj_cell * o) { lean_vm_check(is_external(o)); return static_cast<vm_external*>(o); }
LEAN_ALWAYS_INLINE inline vm_native_closure * to_native_closure(vm_obj_cell * o) { lean_vm_check(is_native_closure(o)); return static_cast<vm_native_closure*>(o); }
// =======================================

// =======================================
// Accessors
LEAN_ALWAYS_INLINE inline unsigned cidx(vm_obj const & o) {
    lean_vm_check(is_simple(o) || is_constructor(o));
    return LEAN_VM_IS_PTR(o.raw()) ? to_composite(o.raw())->idx() : static_cast<unsigned>(LEAN_VM_UNBOX(o.raw()));
}
LEAN_ALWAYS_INLINE inline unsigned csize(vm_obj const & o) { lean_vm_check(is_composite(o)); return to_composite(o)->size(); }
LEAN_ALWAYS_INLINE inline unsigned cfn_idx(vm_obj const & o) { lean_vm_check(is_closure(o)); return to_composite(o)->idx(); }
LEAN_ALWAYS_INLINE inline vm_obj const * cfields(vm_obj const & o) {
    lean_vm_check(is_composite(o)); return to_composite(o)->fields();
}
LEAN_ALWAYS_INLINE inline vm_obj const & cfield(vm_obj const & o, unsigned i) { lean_vm_check(i < csize(o)); return cfields(o)[i]; }
LEAN_ALWAYS_INLINE inline bool to_bool(vm_obj const & o) { return cidx(o) != 0; }
// =======================================

#define LEAN_MAX_SMALL_NAT (1u << 31)

class vm_state;

/** Builtin functions that take arguments from the VM stack. */
typedef void (*vm_function)(vm_state & s);

/** Custom 'cases' operators. Given an object \c o, it returns the constructor index and stores
    the data stored in the object in the buffer \c data. */
typedef unsigned (*vm_cases_function)(vm_obj const & o, buffer<vm_obj> & data);

typedef pair<name, optional<expr>> vm_local_info;

/** \brief VM instruction opcode */
enum class opcode {
    Push, Move, Ret, Drop, Goto,
    SConstructor, Constructor, Num,
    Destruct, Cases2, CasesN, NatCases, BuiltinCases, Proj,
    Apply, InvokeGlobal, InvokeBuiltin, InvokeCFun,
    Closure, Unreachable, Expr, LocalInfo
};

/** \brief VM instructions */
class vm_instr {
    opcode m_op;
    union {
        struct {
            unsigned m_fn_idx;  /* InvokeGlobal, InvokeBuiltin, InvokeCFun and Closure. */
            unsigned m_nargs;   /* Closure */
        };
        /* Push, Move, Proj */
        unsigned m_idx;
        /* Drop */
        unsigned m_num;
        /* Goto, Cases2 and NatCases */
        struct {
            unsigned m_pc[2];
        };
        /* CasesN and BuiltinCases */
        struct {
            unsigned   m_cases_idx; /* only used for BuiltinCases */
            unsigned * m_npcs;
        };
        /* Constructor, SConstructor */
        struct {
            unsigned m_cidx;
            unsigned m_nfields; /* only used by Constructor */
        };
        /* Num */
        mpz * m_mpz;
        /* Expr */
        expr * m_expr;
        /* LocalInfo */
        struct {
            unsigned        m_local_idx;
            vm_local_info * m_local_info;
        };
    };
    /* Apply, Ret, Destruct and Unreachable do not have arguments */
    friend vm_instr mk_push_instr(unsigned idx);
    friend vm_instr mk_move_instr(unsigned idx);
    friend vm_instr mk_drop_instr(unsigned n);
    friend vm_instr mk_proj_instr(unsigned n);
    friend vm_instr mk_goto_instr(unsigned pc);
    friend vm_instr mk_sconstructor_instr(unsigned cidx);
    friend vm_instr mk_constructor_instr(unsigned cidx, unsigned nfields);
    friend vm_instr mk_num_instr(mpz const & v);
    friend vm_instr mk_ret_instr();
    friend vm_instr mk_destruct_instr();
    friend vm_instr mk_unreachable_instr();
    friend vm_instr mk_nat_cases_instr(unsigned pc1, unsigned pc2);
    friend vm_instr mk_cases2_instr(unsigned pc1, unsigned pc2);
    friend vm_instr mk_casesn_instr(unsigned num_pc, unsigned const * pcs);
    friend vm_instr mk_builtin_cases_instr(unsigned cases_idx, unsigned num_pc, unsigned const * pcs);
    friend vm_instr mk_apply_instr();
    friend vm_instr mk_invoke_global_instr(unsigned fn_idx);
    friend vm_instr mk_invoke_cfun_instr(unsigned fn_idx);
    friend vm_instr mk_invoke_builtin_instr(unsigned fn_idx);
    friend vm_instr mk_closure_instr(unsigned fn_idx, unsigned n);
    friend vm_instr mk_expr_instr(expr const &e);
    friend vm_instr mk_local_info_instr(unsigned idx, name const & n, optional<expr> const & e);

    void release_memory();
    void copy_args(vm_instr const & i);
public:
    vm_instr():m_op(opcode::Ret) {}
    vm_instr(opcode op):m_op(op) {}
    vm_instr(vm_instr const & i);
    vm_instr(vm_instr && i);
    ~vm_instr();

    vm_instr & operator=(vm_instr const & s);
    vm_instr & operator=(vm_instr && s);

    opcode op() const { return m_op; }

    unsigned get_fn_idx() const {
        lean_assert(m_op == opcode::InvokeGlobal || m_op == opcode::InvokeBuiltin ||
                    m_op == opcode::InvokeCFun || m_op == opcode::Closure);
        return m_fn_idx;
    }

    unsigned get_nargs() const {
        lean_assert(m_op == opcode::Closure);
        return m_nargs;
    }

    unsigned get_idx() const {
        lean_assert(m_op == opcode::Push || m_op == opcode::Move || m_op == opcode::Proj);
        return m_idx;
    }

    unsigned get_num() const {
        lean_assert(m_op == opcode::Drop);
        return m_num;
    }

    unsigned get_goto_pc() const {
        lean_assert(m_op == opcode::Goto);
        return m_pc[0];
    }

    void set_goto_pc(unsigned pc) {
        lean_assert(m_op == opcode::Goto);
        m_pc[0] = pc;
    }

    unsigned get_cases2_pc(unsigned i) const {
        lean_assert(m_op == opcode::Cases2 || m_op == opcode::NatCases);
        lean_vm_check(i < 2);
        return m_pc[i];
    }

    void set_cases2_pc(unsigned i, unsigned pc) {
        lean_assert(m_op == opcode::Cases2 || m_op == opcode::NatCases);
        lean_vm_check(i < 2);
        m_pc[i] = pc;
    }

    unsigned get_cases_idx() const {
        lean_assert(m_op == opcode::BuiltinCases);
        return m_cases_idx;
    }

    unsigned get_casesn_size() const {
        lean_assert(m_op == opcode::CasesN || m_op == opcode::BuiltinCases);
        return m_npcs[0];
    }

    unsigned get_casesn_pc(unsigned i) const {
        lean_assert(m_op == opcode::CasesN || m_op == opcode::BuiltinCases);
        lean_vm_check(i < get_casesn_size());
        return m_npcs[i+1];
    }

    void set_casesn_pc(unsigned i, unsigned pc) const {
        lean_assert(m_op == opcode::CasesN || m_op == opcode::BuiltinCases);
        lean_vm_check(i < get_casesn_size());
        m_npcs[i+1] = pc;
    }

    unsigned get_cidx() const {
        lean_assert(m_op == opcode::Constructor || m_op == opcode::SConstructor);
        return m_cidx;
    }

    unsigned get_nfields() const {
        lean_assert(m_op == opcode::Constructor);
        return m_nfields;
    }

    mpz const & get_mpz() const {
        lean_assert(m_op == opcode::Num);
        return *m_mpz;
    }

    expr const & get_expr() const {
        lean_assert(m_op == opcode::Expr);
        return *m_expr;
    }

    unsigned get_local_idx() const {
        lean_assert(m_op == opcode::LocalInfo);
        return m_local_idx;
    }

    vm_local_info const & get_local_info() const {
        lean_assert(m_op == opcode::LocalInfo);
        return *m_local_info;
    }

    unsigned get_num_pcs() const;
    unsigned get_pc(unsigned i) const;
    void set_pc(unsigned i, unsigned pc);

    void display(std::ostream & out) const;

    void serialize(serializer & s, std::function<name(unsigned)> const & idx2name) const;
};

vm_instr mk_push_instr(unsigned idx);
vm_instr mk_move_instr(unsigned idx);
vm_instr mk_drop_instr(unsigned n);
vm_instr mk_proj_instr(unsigned n);
vm_instr mk_goto_instr(unsigned pc);
vm_instr mk_sconstructor_instr(unsigned cidx);
vm_instr mk_constructor_instr(unsigned cidx, unsigned nfields);
vm_instr mk_num_instr(mpz const & v);
vm_instr mk_ret_instr();
vm_instr mk_destruct_instr();
vm_instr mk_unreachable_instr();
vm_instr mk_nat_cases_instr(unsigned pc1, unsigned pc2);
vm_instr mk_cases2_instr(unsigned pc1, unsigned pc2);
vm_instr mk_casesn_instr(unsigned num_pc, unsigned const * pcs);
vm_instr mk_builtin_cases_instr(unsigned cases_idx, unsigned num_pc, unsigned const * pcs);
vm_instr mk_apply_instr();
vm_instr mk_invoke_global_instr(unsigned fn_idx);
vm_instr mk_invoke_cfun_instr(unsigned fn_idx);
vm_instr mk_invoke_builtin_instr(unsigned fn_idx);
vm_instr mk_closure_instr(unsigned fn_idx, unsigned n);
vm_instr mk_expr_instr(expr const &e);
vm_instr mk_local_info_instr(unsigned idx, name const & n, optional<expr> const & e);

class vm_state;
class vm_instr;

enum class vm_decl_kind { Bytecode, Builtin, CFun };

/** \brief VM function/constant declaration cell */
struct vm_decl_cell {
    MK_LEAN_RC();
    vm_decl_kind          m_kind;
    name                  m_name;
    unsigned              m_idx;
    unsigned              m_arity;
    list<vm_local_info>   m_args_info;
    optional<pos_info>    m_pos;
    optional<std::string> m_olean;
    union {
        struct {
            unsigned   m_code_size;
            vm_instr * m_code;
        };
        vm_function   m_fn;
        vm_cfunction  m_cfn;
    };
    vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_function fn);
    vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_cfunction fn);
    vm_decl_cell(name const & n, unsigned idx, unsigned arity, unsigned code_sz, vm_instr const * code,
                 list<vm_local_info> const & args_info, optional<pos_info> const & pos,
                 optional<std::string> const & olean);
    ~vm_decl_cell();
    void dealloc();
};

/** \brief VM function/constant declaration smart pointer. */
class vm_decl {
    vm_decl_cell * m_ptr;
    explicit vm_decl(vm_decl_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
public:
    vm_decl():m_ptr(nullptr) {}
    vm_decl(name const & n, unsigned idx, unsigned arity, vm_function fn):
        vm_decl(new vm_decl_cell(n, idx, arity, fn)) {}
    vm_decl(name const & n, unsigned idx, unsigned arity, vm_cfunction fn):
        vm_decl(new vm_decl_cell(n, idx, arity, fn)) {}
    vm_decl(name const & n, unsigned idx, unsigned arity, unsigned code_sz, vm_instr const * code,
            list<vm_local_info> const & args_info, optional<pos_info> const & pos,
            optional<std::string> const & olean = optional<std::string>()):
        vm_decl(new vm_decl_cell(n, idx, arity, code_sz, code, args_info, pos, olean)) {}
    vm_decl(vm_decl const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    vm_decl(vm_decl && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~vm_decl() { if (m_ptr) m_ptr->dec_ref(); }

    friend void swap(vm_decl & a, vm_decl & b) { std::swap(a.m_ptr, b.m_ptr); }

    vm_decl & operator=(vm_decl const & s) { LEAN_COPY_REF(s); }
    vm_decl & operator=(vm_decl && s) { LEAN_MOVE_REF(s); }

    operator bool() const { return m_ptr; }

    vm_decl_kind kind() const { return m_ptr->m_kind; }
    bool is_bytecode() const { lean_assert(m_ptr); return m_ptr->m_kind == vm_decl_kind::Bytecode; }
    bool is_builtin() const { lean_assert(m_ptr); return m_ptr->m_kind == vm_decl_kind::Builtin; }
    bool is_cfun() const { lean_assert(m_ptr); return m_ptr->m_kind == vm_decl_kind::CFun; }
    unsigned get_idx() const { lean_assert(m_ptr); return m_ptr->m_idx; }
    name get_name() const { lean_assert(m_ptr); return m_ptr->m_name; }
    unsigned get_arity() const { lean_assert(m_ptr); return m_ptr->m_arity; }
    unsigned get_code_size() const { lean_assert(is_bytecode()); return m_ptr->m_code_size; }
    vm_instr const * get_code() const { lean_assert(is_bytecode()); return m_ptr->m_code; }
    vm_function get_fn() const { lean_assert(is_builtin()); return m_ptr->m_fn; }
    vm_cfunction get_cfn() const { lean_assert(is_cfun()); return m_ptr->m_cfn; }
    list<vm_local_info> const & get_args_info() const { lean_assert(is_bytecode()); return m_ptr->m_args_info; }
    optional<pos_info> const & get_pos_info() const { lean_assert(is_bytecode()); return m_ptr->m_pos; }
    optional<std::string> const & get_olean() const { lean_assert(is_bytecode()); return m_ptr->m_olean; }
};

/** \brief Virtual machine for executing VM bytecode. */
class vm_state {
    struct performance_counters {
        size_t                      m_num_constructor_allocs{0};
        size_t                      m_num_closure_allocs{0};
        size_t                      m_num_mpz_allocs{0};
    };
public:
    typedef std::vector<vm_decl> decl_vector;
    typedef std::vector<optional<vm_obj>> cache_vector;
    typedef unsigned_map<vm_decl> decl_map;
    typedef std::vector<vm_cases_function> builtin_cases_vector;
    typedef unsigned_map<vm_cases_function> builtin_cases_map;
    environment                 m_env;
    options                     m_options;
    decl_map                    m_decl_map;
    decl_vector                 m_decl_vector;
    cache_vector                m_cache_vector; /* for 0-ary declarations */
    builtin_cases_map           m_builtin_cases_map;
    builtin_cases_vector        m_builtin_cases_vector;
    vm_instr const *            m_code;   /* code of the current function being executed */
    unsigned                    m_fn_idx; /* function idx being executed */
    unsigned                    m_pc;     /* program counter */
    unsigned                    m_bp;     /* base pointer */
    unsigned                    m_next_frame_idx{0};
    bool                        m_profiling{false};
    bool                        m_debugging{false};
    struct frame {
        vm_instr const *        m_code;
        unsigned                m_fn_idx;
        unsigned                m_num;
        unsigned                m_pc;
        unsigned                m_bp;
        unsigned                m_curr_fn_idx;
        /* The following two fields are only used for profiling the code */
        unsigned                m_frame_idx;
        frame(vm_instr const * code, unsigned fn_idx, unsigned num, unsigned pc, unsigned bp,
              unsigned curr_fn_idx, unsigned frame_idx):
            m_code(code), m_fn_idx(fn_idx), m_num(num), m_pc(pc), m_bp(bp),
            m_curr_fn_idx(curr_fn_idx), m_frame_idx(frame_idx) {}
    };
    std::vector<vm_obj>         m_stack;
    std::vector<vm_local_info>  m_stack_info;
    std::vector<frame>          m_call_stack;
    mutex                       m_call_stack_mtx; /* used only when profiling */
    struct debugger_state;
    typedef std::unique_ptr<debugger_state> debugger_state_ptr;
    debugger_state_ptr          m_debugger_state_ptr;
    bool                        m_was_updated{false}; /* set to true if update_env is invoked */

    performance_counters        m_perf_counters;

    void debugger_init();
    void debugger_step();
    void push_local_info(unsigned idx, vm_local_info const & info);
    void shrink_stack_info();
    void stack_pop_back();
    void push_fields(vm_obj const & obj);
    void push_frame_core(unsigned num, unsigned next_pc, unsigned next_fn_idx);
    void push_frame(unsigned num, unsigned next_pc, unsigned next_fn_idx);
    unsigned pop_frame_core();
    unsigned pop_frame();
    void invoke_builtin(vm_decl const & d);
    void invoke_fn(vm_cfunction fn, unsigned arity);
    void invoke_cfun(vm_decl const & d);
    void invoke_global(vm_decl const & d);
    void invoke(vm_decl const & d);
    void run();
    void execute(vm_instr const * code);
    vm_obj invoke_closure(vm_obj const & fn, unsigned nargs);

    vm_decl const & get_decl(unsigned idx) const;

    vm_cases_function const & get_builtin_cases(unsigned idx) const;

public:
    vm_state(environment const & env, options const & opts);
    ~vm_state();

    environment const & env() const { return m_env; }

    void update_env(environment const & env);
    bool env_was_updated() const { return m_was_updated; }

    bool profiling() const { return m_profiling; }

    /* Auxiliary object for temporarily resetting env_was_updated flag. */
    class reset_env_was_updated_flag {
        vm_state & m_state;
        bool       m_old_value;
    public:
        reset_env_was_updated_flag(vm_state & s):
            m_state(s),
            m_old_value(s.m_was_updated) {
            s.m_was_updated = false;
        }
        ~reset_env_was_updated_flag() {
            m_state.m_was_updated = m_old_value || m_state.m_was_updated;
        }
    };

    options const & get_options() const { return m_options; }

    /** \brief Push object into the data stack */
    void push(vm_obj const & o) { m_stack.push_back(o); }

    unsigned stack_size() const { return m_stack.size(); }

    vm_obj const & get_core(unsigned idx) const {
        lean_assert(idx < m_stack.size());
        return m_stack[idx];
    }

    vm_local_info get_info(unsigned idx) const {
        if (idx >= m_stack_info.size())
            return vm_local_info(name(), none_expr());
        else
            return m_stack_info[idx];
    }

    unsigned call_stack_size() const { return m_call_stack.size(); }

    name call_stack_fn(unsigned idx) const {
        lean_assert(idx < m_call_stack.size());
        // m_curr_fn_idx may be equal to g_null_fn_idx
        if (auto decl = m_decl_map.find(m_call_stack[idx].m_curr_fn_idx)) {
            return decl->get_name();
        } else {
            return name();
        }
    }

    unsigned call_stack_bp(unsigned idx) const {
        lean_assert(idx < m_call_stack.size());
        return m_call_stack[idx].m_bp;
    }

    unsigned bp() const { return m_bp; }

    unsigned pc() const { return m_pc; }

    /** \brief Retrieve object from the call stack */
    vm_obj const & get(int idx) const {
        lean_assert(idx + static_cast<int>(m_bp) >= 0);
        lean_assert(m_bp + idx < m_stack.size());
        return m_stack[m_bp + idx];
    }

    vm_obj const & top() const { return m_stack.back(); }

    optional<vm_decl> get_decl(name const & n) const;

    optional<name> curr_fn() const;

    void invoke_fn(name const & fn);
    void invoke_fn(unsigned fn_idx);

    /** Given a stack of the form

            v_n
            ...
            v_1
            (closure ...)

       execute n function applications. */
    void apply(unsigned n = 1);

    void display_stack(std::ostream & out) const;
    void display(std::ostream & out, vm_obj const & o) const;
    void display_call_stack(std::ostream & out) const;
    void display_registers(std::ostream & out) const;

    /** \brief Invoke closure \c fn with the given arguments. These procedures are meant to be use by
        C++ generated/extracted code. */
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                  vm_obj const & a5);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                  vm_obj const & a5, vm_obj const & a6);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                  vm_obj const & a5, vm_obj const & a6, vm_obj const & a7);
    vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                  vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8);
    vm_obj invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args);

    /** \brief Similar to invoke, but catches exceptions and put VM in a consistent state, and return none. */
    optional<vm_obj> try_invoke_catch(vm_obj const & fn, unsigned nargs, vm_obj const * args);

    /** \brief Invoke fn_idx with nargs arguments and return the result */
    vm_obj invoke(unsigned fn_idx, unsigned nargs, vm_obj const * as);
    vm_obj invoke(unsigned fn_idx, std::initializer_list<vm_obj> const & as) {
        return invoke(fn_idx, as.size(), as.begin());
    }
    vm_obj invoke(unsigned fn_idx, vm_obj const & a) {
        return invoke(fn_idx, 1, &a);
    }

    vm_obj invoke(name const & fn, unsigned nargs, vm_obj const * as);
    vm_obj invoke(name const & fn, std::initializer_list<vm_obj> const & as) {
        return invoke(fn, as.size(), as.begin());
    }
    vm_obj invoke(name const & fn, vm_obj const & a) {
        return invoke(fn, 1, &a);
    }
    vm_obj get_constant(name const & cname);

    class profiler {
        typedef std::unique_ptr<interruptible_thread> thread_ptr;
        struct snapshot_core {
            chrono::milliseconds                  m_duration;
            std::vector<pair<unsigned, unsigned>> m_stack;
            performance_counters                  m_perf_counters;
        };
        vm_state &                 m_state;
        atomic<bool>               m_stop;
        unsigned                   m_freq_ms;
        thread_ptr                 m_thread_ptr;
        std::vector<snapshot_core> m_snapshots;
        void stop();
    public:
        profiler(vm_state & s, options const & opts);
        ~profiler();

        struct snapshot {
            chrono::milliseconds              m_duration;
            std::vector<pair<name, unsigned>> m_stack;
            performance_counters              m_perf_counters;
        };

        struct snapshots {
            std::vector<snapshot>                         m_snapshots;
            std::vector<pair<name, chrono::milliseconds>> m_cum_times;
            chrono::milliseconds                          m_total_time;
            bool display(std::string const & what, options const & opts, std::ostream & out) const;
            void display(std::ostream & out) const;
        };
        bool enabled() const { return m_thread_ptr.get() != nullptr; }
        snapshots get_snapshots();
    };

    /* performance counters */
    void inc_constructor_allocs() { m_perf_counters.m_num_constructor_allocs++; }
    void inc_closure_allocs() { m_perf_counters.m_num_closure_allocs++; }
    void inc_mpz_allocs() { m_perf_counters.m_num_mpz_allocs++; }
    performance_counters const & get_perf_counters() const { return m_perf_counters; }
};

/** \brief Helper class for setting thread local vm_state object */
class scope_vm_state {
    vm_state * m_prev;
public:
    scope_vm_state(vm_state & s);
    ~scope_vm_state();
};

/** \brief Return reference to thread local VM state object. */
vm_state & get_vm_state();

/** \brief Return reference to thread local VM state object being debugged. */
vm_state & get_vm_state_being_debugged();

/** \brief Add builtin implementation for the function named \c n.
    All environment objects will contain this builtin.
    \pre These procedures can only be invoked at initialization time. */
void declare_vm_builtin(name const & n, char const * internal_name, unsigned arity, vm_function fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_0 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_1 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_2 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_3 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_4 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_5 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_6 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_7 fn);
void declare_vm_builtin(name const & n, char const * internal_name, vm_cfunction_8 fn);
void declare_vm_builtin(name const & n, char const * internal_name, unsigned arity, vm_cfunction_N fn);

#define DECLARE_VM_BUILTIN(n, fn) declare_vm_builtin(n, #fn, fn)

/** \brief Add builtin implementation for a cases_on */
void declare_vm_cases_builtin(name const & n, char const * internal_name, vm_cases_function fn);

#define DECLARE_VM_CASES_BUILTIN(n, fn) declare_vm_cases_builtin(n, #fn, fn)

/** \brief Return builtin cases internal index. */
optional<unsigned> get_vm_builtin_cases_idx(environment const & env, name const & n);

/** Register in the given environment \c fn as the implementation for function \c n.
    These APIs should be used when we dynamically load native code stored in a shared object (aka DLL)
    that implements lean functions. */
environment add_native(environment const & env, name const & n, vm_cfunction_0 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_1 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_2 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_3 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_4 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_5 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_6 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_7 fn);
environment add_native(environment const & env, name const & n, vm_cfunction_8 fn);
environment add_native(environment const & env, name const & n, unsigned arity, vm_cfunction_N fn);

unsigned get_vm_index(name const & n);
unsigned get_vm_index_bound();
name get_vm_name(unsigned idx);
optional<name> find_vm_name(unsigned idx);

/** \brief Reserve an index for the given function in the VM, the expression
    \c e is the value of \c fn after preprocessing. \c e is used to compute the arity of fn.
    See library/compiler/pre_proprocess_rec.cpp for details. */
environment reserve_vm_index(environment const & env, name const & fn, expr const & e);

/** Lower level version of the previous function. */
environment reserve_vm_index(environment const & env, name const & fn, unsigned arity);

unsigned get_num_nested_lambdas(expr const & e);

/** \brief Add bytcode for the function named \c fn in \c env.
    \remark The index for \c fn must have been reserved using reserve_vm_index. */
environment update_vm_code(environment const & env, name const & fn, unsigned code_sz, vm_instr const * code,
                           list<vm_local_info> const & args_info, optional<pos_info> const & pos);

/** \brief Combines reserve_vm_index and update_vm_code */
environment add_vm_code(environment const & env, name const & fn, expr const & e, unsigned code_sz, vm_instr const * code,
                        list<vm_local_info> const & args_info, optional<pos_info> const & pos);
environment add_vm_code(environment const & env, name const & fn, unsigned arity, unsigned code_sz, vm_instr const * code,
                        list<vm_local_info> const & args_info, optional<pos_info> const & pos);

/** \brief Return the internal idx for the given constant. Return none
    if the constant is not builtin nor it has code associated with it. */
optional<unsigned> get_vm_constant_idx(environment const & env, name const & n);

/** \brief Return true iff \c fn is a VM function in the given environment. */
bool is_vm_function(environment const & env, name const & fn);

optional<vm_decl> get_vm_decl(environment const & env, name const & n);

/** \brief Return the function idx of a builtin function.
    \remark This function must only be invoked after initialize_vm was invoked. */
optional<unsigned> get_vm_builtin_idx(name const & fn);

/** \brief Return true iff \c fn is implemented in C++. */
bool is_vm_builtin_function(name const & fn);
/** \brief Return the name of the C++ function that implements the builtin named \c fn.
    Return nullptr if \c fn is not a builtin. */
char const * get_vm_builtin_internal_name(name const & fn);

enum class vm_builtin_kind { VMFun, CFun, Cases };

/** \brief Return the kind of a builtin function.
    \pre is_vm_builtin_function(fn) */
vm_builtin_kind get_vm_builtin_kind(name const & fn);

/** \brief Return the arity of the C++ function that implements the builtin \c fn.
    \pre is_vm_builtin_function(fn) && get_vm_builtin_kind(fn) == vm_builtin_kind::CFun */
unsigned get_vm_builtin_arity(name const & fn);

environment load_external_fn(environment & env, name const & extern_n);
// void* get_extern_symbol(std::string library_name, std::string extern_name);

/** \brief Invoke closure \c fn with the given arguments. These procedures are meant to be use by
    C++ generated/extracted code. */
vm_obj invoke(vm_obj const & fn, vm_obj const & a1);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7);
vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8);
vm_obj invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args);

vm_obj invoke(unsigned fn_idx, unsigned nargs, vm_obj const * args);
vm_obj invoke(unsigned fn_idx, vm_obj const & arg);

void display_vm_code(std::ostream & out, unsigned code_sz, vm_instr const * code);

environment vm_monitor_register(environment const & env, name const & d);

void initialize_vm_core();
void finalize_vm_core();

void initialize_vm();
void finalize_vm();
}
