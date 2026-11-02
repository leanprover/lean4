/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Joachim Breitner
*/
#include <vector>
#include <limits>
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "util/name_map.h"
#include "kernel/kernel_vm.h"
#include "kernel/expr_maps.h"
#include "kernel/kernel_exception.h"

/* This file must agree exactly with the reference semantics in `src/Init/KernelVM.lean`. */

namespace lean {
static name * g_kvm_prog_mk = nullptr;
static name * g_list_nil    = nullptr;
static name * g_list_cons   = nullptr;
static name * g_nat_zero_n  = nullptr;
static name_map<unsigned> * g_binops = nullptr;
static name_map<unsigned> * g_exp_ctors = nullptr;
static name_map<unsigned> * g_stmt_ctors = nullptr;

/* Memory is limited to this many words; registers to this many registers. */
static size_t const KVM_MAX_MEM_WORDS = 16 * 1024 * 1024;
static size_t const KVM_MAX_REGS = 1 << 16;

enum class binop : uint8 {
    add, sub, mul, udiv, umod, band, bor, bxor, shl, shr, eq, ult, ule, slt, sle,
    sadd, ssub, smul, sdiv, smod
};
static char const * const g_binop_names[] = {
    "add", "sub", "mul", "udiv", "umod", "and", "or", "xor", "shl", "shr", "eq", "ult", "ule",
    "slt", "sle", "sadd", "ssub", "smul", "sdiv", "smod"
};

enum class exp_kind : uint8 { cnst, reg, bin, load, input };
static char const * const g_exp_names[] = { "const", "reg", "bin", "load", "input" };

enum class stmt_kind : uint8 { skip, set, store, seq, ite, loop, assert };
static char const * const g_stmt_names[] = { "skip", "set", "store", "seq", "ite", "while", "assert" };

struct vm_exp {
    exp_kind m_kind;
    binop    m_op;
    uint64   m_val; // constant value, register index or input index
    unsigned m_a;
    unsigned m_b;
};

struct vm_stmt {
    stmt_kind m_kind;
    uint64    m_reg;
    unsigned  m_e1;
    unsigned  m_e2;
    unsigned  m_s1;
    unsigned  m_s2;
};

/* The low 64 bits of `n`. */
static uint64 nat_low64(nat const & n) {
    if (n.is_small()) return n.get_small_value();
    return n.get_big_value().extract_bits64(0);
}

static uint64 nat_get_uint64_at(nat const & n, uint64 off) {
    if (n.is_small()) {
        uint64 v = n.get_small_value();
        return off >= 8 ? 0 : v >> (8 * off);
    }
    mpz const & m = n.get_big_value();
    if (off >= m.size_in_bytes()) return 0;
    return m.extract_bits64(8 * off);
}

uint64 nat_get_uint64(nat const & n, nat const & i) {
    return i.is_small() ? nat_get_uint64_at(n, i.get_small_value()) : 0;
}

/* Thrown when the program term is not of the expected shape. */
struct vm_decode_failure {};

class kernel_vm {
    environment const &                         m_env;
    std::function<expr(expr const &)> const &   m_whnf;
    std::vector<vm_exp>                          m_exps;
    std::vector<vm_stmt>                         m_stmts;
    expr_map<unsigned>                           m_exp_cache;
    expr_map<unsigned>                           m_stmt_cache;
    std::vector<nat>                             m_inputs;
    std::vector<uint64>                          m_regs;
    std::vector<uint64>                          m_mem;
    size_t                                       m_num_regs = 0;
    unsigned                                     m_ticks = 0;

    nat decode_nat(expr const & e) {
        expr v = m_whnf(e);
        if (is_constant(v) && const_name(v) == *g_nat_zero_n) return nat(0u);
        if (!is_nat_lit(v)) throw vm_decode_failure();
        return lit_value(v).get_nat();
    }

    /* Returns the constructor index of `v` in `ctors` and its arguments. */
    unsigned decode_ctor(expr const & v, name_map<unsigned> const & ctors, buffer<expr> & args) {
        expr const & fn = get_app_args(v, args);
        if (!is_constant(fn)) throw vm_decode_failure();
        unsigned const * idx = ctors.find(const_name(fn));
        if (!idx) throw vm_decode_failure();
        return *idx;
    }

    unsigned decode_exp(expr const & e) {
        auto it = m_exp_cache.find(e);
        if (it != m_exp_cache.end()) return it->second;
        buffer<expr> args;
        vm_exp r { exp_kind::cnst, binop::add, 0, 0, 0 };
        switch (static_cast<exp_kind>(decode_ctor(m_whnf(e), *g_exp_ctors, args))) {
        case exp_kind::cnst:
            if (args.size() != 1) throw vm_decode_failure();
            r.m_val = nat_low64(decode_nat(args[0]));
            break;
        case exp_kind::reg: {
            if (args.size() != 1) throw vm_decode_failure();
            r.m_kind = exp_kind::reg;
            r.m_val  = decode_reg(args[0]);
            break;
        }
        case exp_kind::bin: {
            if (args.size() != 3) throw vm_decode_failure();
            buffer<expr> op_args;
            r.m_kind = exp_kind::bin;
            r.m_op   = static_cast<binop>(decode_ctor(m_whnf(args[0]), *g_binops, op_args));
            if (!op_args.empty()) throw vm_decode_failure();
            r.m_a    = decode_exp(args[1]);
            r.m_b    = decode_exp(args[2]);
            break;
        }
        case exp_kind::load:
            if (args.size() != 1) throw vm_decode_failure();
            r.m_kind = exp_kind::load;
            r.m_a    = decode_exp(args[0]);
            break;
        case exp_kind::input: {
            if (args.size() != 2) throw vm_decode_failure();
            nat k = decode_nat(args[0]);
            r.m_kind = exp_kind::input;
            // Indices beyond the inputs read as `0`, whatever their value.
            r.m_val  = k.is_small() ? k.get_small_value() : std::numeric_limits<uint64>::max();
            r.m_a    = decode_exp(args[1]);
            break;
        }
        }
        unsigned idx = m_exps.size();
        m_exps.push_back(r);
        m_exp_cache.insert(mk_pair(e, idx));
        return idx;
    }

    uint64 decode_reg(expr const & e) {
        nat i = decode_nat(e);
        if (!i.is_small() || i.get_small_value() >= KVM_MAX_REGS)
            throw kernel_exception(m_env, sstream() << "the kernel VM supports at most "
                                   << KVM_MAX_REGS << " registers");
        uint64 r = i.get_small_value();
        if (r >= m_num_regs) m_num_regs = r + 1;
        return r;
    }

    unsigned decode_stmt(expr const & e) {
        auto it = m_stmt_cache.find(e);
        if (it != m_stmt_cache.end()) return it->second;
        buffer<expr> args;
        vm_stmt r { stmt_kind::skip, 0, 0, 0, 0, 0 };
        r.m_kind = static_cast<stmt_kind>(decode_ctor(m_whnf(e), *g_stmt_ctors, args));
        switch (r.m_kind) {
        case stmt_kind::skip:
            if (args.size() != 0) throw vm_decode_failure();
            break;
        case stmt_kind::set:
            if (args.size() != 2) throw vm_decode_failure();
            r.m_reg = decode_reg(args[0]);
            r.m_e1  = decode_exp(args[1]);
            break;
        case stmt_kind::store:
            if (args.size() != 2) throw vm_decode_failure();
            r.m_e1 = decode_exp(args[0]);
            r.m_e2 = decode_exp(args[1]);
            break;
        case stmt_kind::seq:
            if (args.size() != 2) throw vm_decode_failure();
            r.m_s1 = decode_stmt(args[0]);
            r.m_s2 = decode_stmt(args[1]);
            break;
        case stmt_kind::ite:
            if (args.size() != 3) throw vm_decode_failure();
            r.m_e1 = decode_exp(args[0]);
            r.m_s1 = decode_stmt(args[1]);
            r.m_s2 = decode_stmt(args[2]);
            break;
        case stmt_kind::loop:
            if (args.size() != 2) throw vm_decode_failure();
            r.m_e1 = decode_exp(args[0]);
            r.m_s1 = decode_stmt(args[1]);
            break;
        case stmt_kind::assert:
            if (args.size() != 1) throw vm_decode_failure();
            r.m_e1 = decode_exp(args[0]);
            break;
        }
        unsigned idx = m_stmts.size();
        m_stmts.push_back(r);
        m_stmt_cache.insert(mk_pair(e, idx));
        return idx;
    }

    static bool of_signed(int64 v, uint64 & r) { r = static_cast<uint64>(v); return true; }

    /* `Int.ediv`/`Int.emod` on 64-bit integers; `b ≠ 0` and not `INT64_MIN / -1`. */
    static int64 ediv(int64 a, int64 b) {
        int64 q = a / b, r = a % b;
        if (r < 0) q = b > 0 ? q - 1 : q + 1;
        return q;
    }
    static int64 emod(int64 a, int64 b) {
        int64 r = a % b;
        if (r < 0) r = b > 0 ? r + b : r - b;
        return r;
    }

    static bool eval_binop(binop op, uint64 a, uint64 b, uint64 & r) {
        int64 sa = static_cast<int64>(a), sb = static_cast<int64>(b), sr;
        switch (op) {
        case binop::add:  r = a + b; return true;
        case binop::sub:  r = a - b; return true;
        case binop::mul:  r = a * b; return true;
        case binop::udiv: r = b == 0 ? 0 : a / b; return true;
        case binop::umod: r = b == 0 ? a : a % b; return true;
        case binop::band: r = a & b; return true;
        case binop::bor:  r = a | b; return true;
        case binop::bxor: r = a ^ b; return true;
        case binop::shl:  r = a << (b % 64); return true;
        case binop::shr:  r = a >> (b % 64); return true;
        case binop::eq:   r = a == b; return true;
        case binop::ult:  r = a < b; return true;
        case binop::ule:  r = a <= b; return true;
        case binop::slt:  r = sa < sb; return true;
        case binop::sle:  r = sa <= sb; return true;
        case binop::sadd: if (__builtin_add_overflow(sa, sb, &sr)) return false; return of_signed(sr, r);
        case binop::ssub: if (__builtin_sub_overflow(sa, sb, &sr)) return false; return of_signed(sr, r);
        case binop::smul: if (__builtin_mul_overflow(sa, sb, &sr)) return false; return of_signed(sr, r);
        case binop::sdiv:
            if (sb == 0) { r = 0; return true; }
            // `INT64_MIN / -1 = 2^63` does not fit.
            if (sa == std::numeric_limits<int64>::min() && sb == -1) return false;
            return of_signed(ediv(sa, sb), r);
        case binop::smod:
            if (sb == 0) { r = a; return true; }
            if (sb == -1) { r = 0; return true; }
            return of_signed(emod(sa, sb), r);
        }
        lean_unreachable();
    }

    bool eval(unsigned ei, uint64 & r) {
        vm_exp const & e = m_exps[ei];
        switch (e.m_kind) {
        case exp_kind::cnst: r = e.m_val; return true;
        case exp_kind::reg:  r = m_regs[e.m_val]; return true;
        case exp_kind::bin: {
            uint64 a, b;
            if (!eval(e.m_a, a) || !eval(e.m_b, b)) return false;
            return eval_binop(e.m_op, a, b, r);
        }
        case exp_kind::load: {
            uint64 a;
            if (!eval(e.m_a, a)) return false;
            r = a < m_mem.size() ? m_mem[a] : 0;
            return true;
        }
        case exp_kind::input: {
            uint64 off;
            if (!eval(e.m_a, off)) return false;
            r = e.m_val < m_inputs.size() ? nat_get_uint64_at(m_inputs[e.m_val], off) : 0;
            return true;
        }
        }
        lean_unreachable();
    }

    void store(uint64 addr, uint64 v) {
        if (addr >= m_mem.size()) {
            if (addr >= KVM_MAX_MEM_WORDS)
                throw kernel_exception(m_env, sstream() << "the kernel VM ran out of memory: "
                                       "address " << addr << " exceeds the limit of "
                                       << KVM_MAX_MEM_WORDS << " words");
            m_mem.resize(addr + 1, 0);
        }
        m_mem[addr] = v;
    }

    /* `Stmt.exec inputs fuel s`; returns `false` where it returns `none`. */
    bool exec(uint64 fuel, unsigned si) {
        if (fuel == 0) return false;
        vm_stmt const & s = m_stmts[si];
        switch (s.m_kind) {
        case stmt_kind::skip: return true;
        case stmt_kind::set: {
            uint64 v;
            if (!eval(s.m_e1, v)) return false;
            m_regs[s.m_reg] = v;
            return true;
        }
        case stmt_kind::store: {
            uint64 a, v;
            if (!eval(s.m_e1, a) || !eval(s.m_e2, v)) return false;
            store(a, v);
            return true;
        }
        case stmt_kind::seq:
            return exec(fuel - 1, s.m_s1) && exec(fuel - 1, s.m_s2);
        case stmt_kind::ite: {
            uint64 c;
            if (!eval(s.m_e1, c)) return false;
            return exec(fuel - 1, c != 0 ? s.m_s1 : s.m_s2);
        }
        case stmt_kind::loop:
            // Iteration `k` (from `0`) runs the body with fuel `fuel - k - 1`.
            for (uint64 f = fuel; ; f--) {
                if (f == 0) return false;
                uint64 c;
                if (!eval(s.m_e1, c)) return false;
                if (c == 0) return true;
                if (!exec(f - 1, s.m_s1)) return false;
                if (++m_ticks == 0) check_system("kernel VM", /* do_check_interrupted */ true);
            }
        case stmt_kind::assert: {
            uint64 c;
            if (!eval(s.m_e1, c)) return false;
            return c != 0;
        }
        }
        lean_unreachable();
    }

public:
    kernel_vm(environment const & env, std::function<expr(expr const &)> const & whnf):
        m_env(env), m_whnf(whnf) {}

    optional<bool> run(expr const & prog, expr const & inputs, expr const & fuel) {
        unsigned body;
        uint64 fuel_v;
        try {
            buffer<expr> args;
            expr p = m_whnf(prog);
            expr const & fn = get_app_args(p, args);
            if (!is_constant(fn) || const_name(fn) != *g_kvm_prog_mk || args.size() != 1)
                return optional<bool>();
            body = decode_stmt(args[0]);
            expr l = m_whnf(inputs);
            while (true) {
                buffer<expr> largs;
                expr const & lfn = get_app_args(l, largs);
                if (!is_constant(lfn)) return optional<bool>();
                if (const_name(lfn) == *g_list_nil && largs.size() == 1) break;
                if (const_name(lfn) != *g_list_cons || largs.size() != 3) return optional<bool>();
                m_inputs.push_back(decode_nat(largs[1]));
                l = m_whnf(largs[2]);
            }
            nat f = decode_nat(fuel);
            // Fuel beyond `2^64 - 1` cannot run out in practice.
            fuel_v = f.is_small() ? f.get_small_value() : std::numeric_limits<uint64>::max();
        } catch (vm_decode_failure &) {
            return optional<bool>();
        }
        m_regs.assign(m_num_regs, 0);
        return optional<bool>(exec(fuel_v, body));
    }
};

optional<bool> kernel_vm_run(environment const & env, expr const & e,
                             std::function<expr(expr const &)> const & whnf) {
    expr const & fuel   = app_arg(e);
    expr const & inputs = app_arg(app_fn(e));
    expr const & prog   = app_arg(app_fn(app_fn(e)));
    kernel_vm vm(env, whnf);
    return vm.run(prog, inputs, fuel);
}

static void register_ctors(name_map<unsigned> & m, name const & prefix,
                           char const * const * names, unsigned n) {
    for (unsigned i = 0; i < n; i++)
        m.insert(name(prefix, names[i]), i);
}

void initialize_kernel_vm() {
    g_kvm_prog_mk = new name{"Lean", "KernelVM", "Prog", "mk"};
    g_list_nil    = new name{"List", "nil"};
    g_list_cons   = new name{"List", "cons"};
    g_nat_zero_n  = new name{"Nat", "zero"};
    g_binops      = new name_map<unsigned>();
    g_exp_ctors   = new name_map<unsigned>();
    g_stmt_ctors  = new name_map<unsigned>();
    register_ctors(*g_binops, name{"Lean", "KernelVM", "BinOp"}, g_binop_names,
                   sizeof(g_binop_names) / sizeof(g_binop_names[0]));
    register_ctors(*g_exp_ctors, name{"Lean", "KernelVM", "Exp"}, g_exp_names,
                   sizeof(g_exp_names) / sizeof(g_exp_names[0]));
    register_ctors(*g_stmt_ctors, name{"Lean", "KernelVM", "Stmt"}, g_stmt_names,
                   sizeof(g_stmt_names) / sizeof(g_stmt_names[0]));
}

void finalize_kernel_vm() {
    delete g_kvm_prog_mk;
    delete g_list_nil;
    delete g_list_cons;
    delete g_nat_zero_n;
    delete g_binops;
    delete g_exp_ctors;
    delete g_stmt_ctors;
}
}
