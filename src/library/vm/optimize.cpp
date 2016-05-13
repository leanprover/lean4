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
    unsigned i = code.size() - 1;
    while (i > 0) {
        --i;
        if (code[i].op() == opcode::Drop &&
            code[i+1].op() == opcode::Drop) {
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

void optimize(environment const &, buffer<vm_instr> & code) {
    compress_goto_ret(code);
    compress_drop_drop(code);
}
}
