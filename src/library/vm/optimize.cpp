/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"

namespace lean {
static void del_instr_at(unsigned pc, buffer<vm_instr> & code) {
    code.erase(pc);
    // we must adjust pc of other instructions
    for (unsigned i = 0; i < code.size(); i++) {
        vm_instr & c = code[i];
        for (unsigned j = 0; j < c.get_num_pcs(); j++) {
            if (c.get_pc(j) > pc)
                c.set_pc(j, c.get_pc(j) - 1);
        }
    }
}

typedef rb_tree<unsigned, unsigned_cmp> addr_set;

/* Collect addresses in addr_set that are goto/branching targets */
static void collect_targets(buffer<vm_instr> & code, addr_set & r) {
    for (auto c : code) {
        for (unsigned j = 0; j < c.get_num_pcs(); j++)
            r.insert(c.get_pc(j));
    }
}

/**
   \brief Applies the following transformation
   ...
   pc:   drop n
   pc+1: drop m
   ...
   ===>
   ...
   pc:   drop n+m
   ... */
static void compress_drop_drop(buffer<vm_instr> & code) {
    if (code.empty()) return;
    addr_set targets;
    collect_targets(code, targets);
    unsigned i = code.size() - 1;
    while (i > 0) {
        --i;
        if (code[i].op() == opcode::Drop &&
            code[i+1].op() == opcode::Drop &&
            /* If i+1 is a goto/branch target, then we should not merge the two Drops */
            !targets.contains(i+1)) {
            code[i] = mk_drop_instr(code[i].get_num() + code[i+1].get_num());
            del_instr_at(i+1, code);
        }
    }
}

/**
   \brief Applies the following transformation

   pc_1 : goto pc_2
   ...
   pc_2 : ret
   ===>
   pc_1 : ret
   ...
   pc_2 : ret */
static void compress_goto_ret(buffer<vm_instr> & code) {
    unsigned i = code.size();
    while (i > 0) {
        --i;
        if (code[i].op() == opcode::Goto) {
            unsigned pc = code[i].get_goto_pc();
            if (code[pc].op() == opcode::Ret) {
                code[i] = mk_ret_instr();
            }
        }
    }
}

typedef rb_tree<unsigned, unsigned_cmp> live_var_set;

class live_vars_fn {
    buffer<vm_instr> const &       m_code;
    buffer<optional<live_var_set>> m_result;

    live_var_set collect(unsigned pc) {
        check_system("live variable analysis");
        if (pc >= m_code.size()) return live_var_set();
        if (auto s = m_result[pc]) return *s; /* already processed */
        auto const & instr = m_code[pc];
        live_var_set s;
        switch (instr.op()) {
        case opcode::Ret: case opcode::Unreachable:
            break;
        case opcode::Goto:
            s = collect(instr.get_goto_pc());
            break;
        case opcode::Drop: case opcode::SConstructor:
        case opcode::Constructor: case opcode::Num: case opcode::String:
        case opcode::Proj: case opcode::Apply: case opcode::InvokeGlobal:
        case opcode::InvokeBuiltin: case opcode::InvokeCFun:
        case opcode::Closure: case opcode::Expr: case opcode::LocalInfo:
        case opcode::Reset: case opcode::Reuse:
            s = collect(pc+1);
            break;
        case opcode::Push: case opcode::Move:
            s = collect(pc+1);
            s.insert(instr.get_idx());
            break;
        case opcode::Cases2:
            s = collect(instr.get_cases2_pc(0));
            s.merge(collect(instr.get_cases2_pc(1)));
            break;
        case opcode::CasesN:
            s = collect(instr.get_casesn_pc(0));
            for (unsigned i = 1; i < instr.get_casesn_size(); i++)
                s.merge(collect(instr.get_casesn_pc(i)));
            break;
        }
        m_result[pc] = optional<live_var_set>(s);
        return s;
    }
public:
    live_vars_fn(buffer<vm_instr> const & c):m_code(c) {
        m_result.resize(c.size());
    }

    buffer<optional<live_var_set>> const & operator()() {
        collect(0);
        return m_result;
    }
};

void convert_push_to_move(buffer<vm_instr> & code) {
    live_vars_fn fn(code);
    buffer<optional<live_var_set>> live_vars_buffer = fn();
    for (unsigned pc = 0; pc < code.size(); pc++) {
        vm_instr & instr = code[pc];
        if (instr.op() == opcode::Push &&
            live_vars_buffer[pc+1] &&
            !live_vars_buffer[pc+1]->contains(instr.get_idx())) {
            instr = mk_move_instr(instr.get_idx());
        }
    }
}

void optimize(environment const &, buffer<vm_instr> & code) {
    compress_goto_ret(code);
    compress_drop_drop(code);
    convert_push_to_move(code);
}
}
