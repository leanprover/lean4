/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.instances init.control.state init.lean.disjoint_set

namespace lean
namespace ir
/-
We need to eliminate Phi nodes before we translate the IR to C/C++.

The procedure is the following. First, for each instruction `x : ty := phi y_1 ... y_n`,
we put `x`, `y_1`, ... `y_n` in the same equivalence class.
Then, we select a representative from each equivalence class and replace each
variable with its representative.
-/
@[reducible] def elim_phi_m (α : Type) := state_t (disjoint_set var) id α

def elim_phi_m.run {α} (a : elim_phi_m α) : α :=
run a (mk_disjoint_set var)

def merge (x y : var) : elim_phi_m unit :=
modify $ λ s, s.merge x y

def find (x : var) : elim_phi_m var :=
do s ← get, pure $ s.find x

def group_vars : decl → elim_phi_m unit
| (decl.defn _ bs) := bs.mfor $ λ b, b.phis.mfor $ λ p, p.ys.mfor (merge p.x)
| _                := pure ()

def instr.replace_vars : instr → elim_phi_m instr
| (instr.assign x ty y)            := instr.assign <$> find x <*> pure ty <*> find y
| (instr.assign_lit x ty lit)      := instr.assign_lit <$> find x <*> pure ty <*> pure lit
| (instr.assign_unop x ty op y)    := instr.assign_unop <$> find x <*> pure ty <*> pure op <*> find y
| (instr.assign_binop x ty op y z) := instr.assign_binop <$> find x <*> pure ty <*> pure op <*> find y <*> find z
| (instr.unop op x)                := instr.unop op <$> find x
| (instr.call x f ys)              := instr.call <$> find x <*> pure f <*> ys.mmap find
| (instr.cnstr o tag n s)          := instr.cnstr <$> find o <*> pure tag <*> pure n <*> pure s
| (instr.set o i x)                := instr.set <$> find o <*> pure i <*> find x
| (instr.get x o i)                := instr.get <$> find x <*> find o <*> pure i
| (instr.sset o i x)               := instr.sset <$> find o <*> pure i <*> find x
| (instr.sget x ty o i)            := instr.sget <$> find x <*> pure ty <*> find o <*> pure i
| (instr.closure x f ys)           := instr.closure <$> find x <*> pure f <*> ys.mmap find
| (instr.apply x ys)               := instr.apply <$> find x <*> ys.mmap find
| (instr.array a sz c)             := instr.array <$> find a <*> find sz <*> find c
| (instr.array_write a i v)        := instr.array_write <$> find a <*> find i <*> find v
| (instr.sarray a ty sz c)         := instr.sarray <$> find a <*> pure ty <*> find sz <*> find c

def terminator.replace_vars : terminator → elim_phi_m terminator
| (terminator.ret x)    := terminator.ret <$> find x
| (terminator.case x bs) := terminator.case <$> find x <*> pure bs
| j@(terminator.jmp _)   := pure j

def arg.replace_vars (a : arg) : elim_phi_m arg :=
do x ← find a.n, pure { n := x, ..a }

def header.replace_vars (h : header) : elim_phi_m header :=
do as ← h.args.mmap arg.replace_vars, pure { args := as, ..h }

def block.replace_vars (b : block) : elim_phi_m block :=
do instrs' ← b.instrs.mmap instr.replace_vars,
   term'   ← b.term.replace_vars,
   pure
     { phis   := [],
       instrs := instrs',
       term   := term', ..b}

def decl.replace_vars : decl → elim_phi_m decl
| (decl.defn h bs) := decl.defn <$> (header.replace_vars h) <*> bs.mmap block.replace_vars
| other            := pure other

def elim_phi_aux (d : decl) : elim_phi_m decl :=
group_vars d *> d.replace_vars

def elim_phi (d : decl) : decl :=
(elim_phi_aux d).run

end ir
end lean
