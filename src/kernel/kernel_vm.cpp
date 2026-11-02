/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Joachim Breitner
*/
#include <vector>
#include <cstring>
#include <limits>
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "util/name_map.h"
#include "kernel/kernel_vm.h"
#include "kernel/expr_maps.h"
#include "kernel/kernel_exception.h"

/* This file must agree exactly with the reference semantics in `src/Init/KernelVM.lean`. */

namespace lean {
static name * g_list_nil    = nullptr;
static name * g_list_cons   = nullptr;
static name * g_nat_zero_n  = nullptr;
static name * g_input_nat   = nullptr;
static name * g_input_str   = nullptr;

/* Memory is limited to this many words. */
static size_t const KVM_MAX_MEM_WORDS = 16 * 1024 * 1024;
static size_t const KVM_NUM_REGS = 1 << 16;

enum class binop : uint8 {
    add, sub, mul, udiv, umod, band, bor, bxor, shl, shr, eq, ult, ule, slt, sle,
    sadd, ssub, smul, sdiv, smod, count
};

/* A decoded instruction, see `Lean.KernelVM.Instr`. */
struct vm_instr {
    uint8  m_opc;
    uint8  m_op;
    uint16 m_d;
    uint16 m_a;
    uint16 m_b;
    uint64 m_imm;
};


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

/* The little-endian bytes of `n` up to its last nonzero word, followed by 8 zero bytes. Assumes a
   little-endian host. */
static std::vector<unsigned char> nat_bytes(nat const & n) {
    size_t num_words = n.is_small() ? 1 : (n.get_big_value().size_in_bytes() + 7) / 8;
    std::vector<unsigned char> r(8 * num_words + 8, 0);
    for (size_t i = 0; i < num_words; i++) {
        uint64 w = nat_get_uint64_at(n, 8 * i);
        memcpy(r.data() + 8 * i, &w, 8);
    }
    return r;
}

/* Thrown when a term is not of the expected shape. */
struct vm_decode_failure {};

/* An input: its bytes, followed by 8 zero bytes so that word reads need no bounds check, and its size
   as `Lean.KernelVM.Input.size`. */
struct vm_input {
    std::vector<unsigned char> m_bytes;
    uint64                     m_size;
};

class kernel_vm {
    environment const &                         m_env;
    std::function<expr(expr const &)> const &   m_whnf;
    std::vector<vm_instr>                        m_code;
    /* The number of instructions, which may exceed `m_code.size()`: the missing ones are zero, that
       is, `halt`. */
    uint64                                       m_num_instrs = 0;
    std::vector<vm_input>                        m_inputs;
    std::vector<uint64>                          m_regs;
    std::vector<uint64>                          m_mem;

    nat decode_nat(expr const & e) {
        expr v = m_whnf(e);
        if (is_constant(v) && const_name(v) == *g_nat_zero_n) return nat(0u);
        if (!is_nat_lit(v)) throw vm_decode_failure();
        return lit_value(v).get_nat();
    }

    void decode_program(nat const & p) {
        m_num_instrs = nat_get_uint64_at(p, 0);
        size_t num_bytes = p.is_small() ? 8 : p.get_big_value().size_in_bytes();
        uint64 available = (num_bytes + 15) / 16;
        uint64 n = std::min(m_num_instrs, available);
        m_code.reserve(n);
        for (uint64 i = 0; i < n; i++) {
            uint64 w   = nat_get_uint64_at(p, 16 * i + 8);
            uint64 imm = nat_get_uint64_at(p, 16 * i + 16);
            m_code.push_back(vm_instr { static_cast<uint8>(w), static_cast<uint8>(w >> 8),
                static_cast<uint16>(w >> 16), static_cast<uint16>(w >> 32), static_cast<uint16>(w >> 48), imm });
        }
    }

    vm_input decode_input(expr const & e) {
        buffer<expr> args;
        expr v = m_whnf(e);
        expr const & fn = get_app_args(v, args);
        if (!is_constant(fn) || args.size() != 1) throw vm_decode_failure();
        if (const_name(fn) == *g_input_nat) {
            nat n = decode_nat(args[0]);
            vm_input r { nat_bytes(n), 0 };
            if (!n.is_zero()) {
                size_t sz = r.m_bytes.size() - 8;
                while (sz > 0 && r.m_bytes[sz - 1] == 0) sz--;
                r.m_size = sz;
            }
            return r;
        } else if (const_name(fn) == *g_input_str) {
            expr s = m_whnf(args[0]);
            if (!is_string_lit(s)) throw vm_decode_failure();
            string_ref const & str = lit_value(s).get_string();
            vm_input r { std::vector<unsigned char>(str.data(), str.data() + str.num_bytes()), str.num_bytes() };
            r.m_bytes.resize(r.m_bytes.size() + 8, 0);
            return r;
        }
        throw vm_decode_failure();
    }

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

    static inline __attribute__((always_inline)) bool eval_binop(uint8 op, uint64 a, uint64 b, uint64 & r) {
        int64 sa = static_cast<int64>(a), sb = static_cast<int64>(b), sr;
        switch (static_cast<binop>(op)) {
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
        case binop::sadd: if (__builtin_add_overflow(sa, sb, &sr)) return false; r = static_cast<uint64>(sr); return true;
        case binop::ssub: if (__builtin_sub_overflow(sa, sb, &sr)) return false; r = static_cast<uint64>(sr); return true;
        case binop::smul: if (__builtin_mul_overflow(sa, sb, &sr)) return false; r = static_cast<uint64>(sr); return true;
        case binop::sdiv:
            if (sb == 0) { r = 0; return true; }
            // `INT64_MIN / -1 = 2^63` does not fit.
            if (sa == std::numeric_limits<int64>::min() && sb == -1) return false;
            r = static_cast<uint64>(ediv(sa, sb)); return true;
        case binop::smod:
            if (sb == 0) { r = a; return true; }
            if (sb == -1) { r = 0; return true; }
            r = static_cast<uint64>(emod(sa, sb)); return true;
        default: return false;
        }
    }

    void store(uint64 addr, uint64 v) {
        if (addr >= m_mem.size()) {
            if (addr >= KVM_MAX_MEM_WORDS)
                throw kernel_exception(m_env, sstream() << "the kernel VM ran out of memory: "
                                       "address " << addr << " exceeds the limit of "
                                       << KVM_MAX_MEM_WORDS << " words");
            m_mem.resize(std::max<size_t>(addr + 1, 2 * m_mem.size()), 0);
        }
        m_mem[addr] = v;
    }

    /* `Lean.KernelVM.exec`. */
    bool exec(uint64 fuel) {
        uint64 * regs = m_regs.data();
        uint64 pc = 0;
        uint64 ticks = 0;
        while (true) {
            if (fuel == 0) return false;
            fuel--;
            if (pc >= m_code.size()) return true;
            if ((++ticks & 0xffffff) == 0) check_system("kernel VM", /* do_check_interrupted */ true);
            vm_instr const & i = m_code[pc];
            switch (i.m_opc) {
            case 0: return true;
            case 1: return false;
            case 2: regs[i.m_d] = i.m_imm; pc++; break;
            case 3: {
                uint64 r;
                if (!eval_binop(i.m_op, regs[i.m_a], regs[i.m_b], r)) return false;
                regs[i.m_d] = r; pc++; break;
            }
            case 4: {
                uint64 r;
                if (!eval_binop(i.m_op, regs[i.m_a], i.m_imm, r)) return false;
                regs[i.m_d] = r; pc++; break;
            }
            case 5: {
                uint64 a = regs[i.m_a] + i.m_imm;
                regs[i.m_d] = a < m_mem.size() ? m_mem[a] : 0;
                pc++; break;
            }
            case 6: store(regs[i.m_a] + i.m_imm, regs[i.m_b]); pc++; break;
            case 7: {
                uint64 r = 0, off = regs[i.m_a];
                if (i.m_imm < m_inputs.size()) {
                    std::vector<unsigned char> const & in = m_inputs[i.m_imm].m_bytes;
                    if (off < in.size() - 8) memcpy(&r, in.data() + off, 8);
                }
                regs[i.m_d] = r; pc++; break;
            }
            case 8: regs[i.m_d] = i.m_imm < m_inputs.size() ? m_inputs[i.m_imm].m_size : 0; pc++; break;
            case 9: pc = i.m_imm; break;
            case 10: pc = regs[i.m_a] == 0 ? i.m_imm : pc + 1; break;
            case 11: pc = regs[i.m_a] != 0 ? i.m_imm : pc + 1; break;
            case 12: if (regs[i.m_a] == 0) return false; pc++; break;
            default: return false;
            }
        }
    }

public:
    kernel_vm(environment const & env, std::function<expr(expr const &)> const & whnf):
        m_env(env), m_whnf(whnf) {}

    optional<bool> run(expr const & prog, expr const & inputs, expr const & fuel) {
        uint64 fuel_v;
        try {
            decode_program(decode_nat(prog));
            expr l = m_whnf(inputs);
            while (true) {
                buffer<expr> largs;
                expr const & lfn = get_app_args(l, largs);
                if (!is_constant(lfn)) return optional<bool>();
                if (const_name(lfn) == *g_list_nil && largs.size() == 1) break;
                if (const_name(lfn) != *g_list_cons || largs.size() != 3) return optional<bool>();
                m_inputs.push_back(decode_input(largs[1]));
                l = m_whnf(largs[2]);
            }
            nat f = decode_nat(fuel);
            // Fuel beyond `2^64 - 1` cannot run out in practice.
            fuel_v = f.is_small() ? f.get_small_value() : std::numeric_limits<uint64>::max();
        } catch (vm_decode_failure &) {
            return optional<bool>();
        }
        m_regs.assign(KVM_NUM_REGS, 0);
        return optional<bool>(exec(fuel_v));
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

void initialize_kernel_vm() {
    g_list_nil    = new name{"List", "nil"};
    g_list_cons   = new name{"List", "cons"};
    g_nat_zero_n  = new name{"Nat", "zero"};
    g_input_nat   = new name{"Lean", "KernelVM", "Input", "nat"};
    g_input_str   = new name{"Lean", "KernelVM", "Input", "str"};
}

void finalize_kernel_vm() {
    delete g_list_nil;
    delete g_list_cons;
    delete g_nat_zero_n;
    delete g_input_nat;
    delete g_input_str;
}
}
