/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.instances init.lean.ir.format

namespace lean
namespace ir
@[reducible] def ssa_pre_m := except_t format (state_t var2blockid id)

def var.declare (x : var) : reader_t blockid ssa_pre_m unit :=
do m ← get,
   if m.contains x then throw ("already defined " ++ to_fmt x)
   else do b ← read, put (m.insert x b)

def instr.declare_vars : instr → reader_t blockid ssa_pre_m unit
| (instr.assign x _ _)           := x.declare
| (instr.assign_lit x _ _)       := x.declare
| (instr.assign_unop x _ _ _)    := x.declare
| (instr.assign_binop x _ _ _ _) := x.declare
| (instr.call x _ _)             := x.declare
| (instr.cnstr o _ _ _)          := o.declare
| (instr.get x _ _)              := x.declare
| (instr.sget x _ _ _)           := x.declare
| (instr.closure x _ _)          := x.declare
| (instr.apply x _)              := x.declare
| (instr.array a _ _)            := a.declare
| (instr.sarray x _ _ _)         := x.declare
| _                              := pure ()

def phi.declare  (p : phi) : reader_t blockid ssa_pre_m unit :=
p.decorate_error p.x.declare

def block.declare_vars (b : block) : ssa_pre_m unit :=
b.decorate_error $ (b.phis.mfor phi.declare *> b.instrs.mfor instr.declare_vars).run b.id

def arg.declare (a : arg) : reader_t blockid ssa_pre_m unit :=
a.n.declare

/- Collect where each variable is declared, and
   check whether each variable was declared at most once. -/
def decl.declare_vars : decl → ssa_pre_m unit
| (decl.defn h (b::bs)) :=
  /- We assume that arguments are declared in the first basic block. -/
  h.decorate_error $ (h.args.mfor arg.declare).run b.id *> b.declare_vars *> bs.mfor block.declare_vars
| (decl.defn _  []) := throw "declaration must have at least one basic block"
| _                 := pure ()

/- Generate the mapping from variable to blockid for the given declaration.
   This function assumes `d` is in SSA. -/
def decl.var2blockid (d : decl) : except format var2blockid :=
run (d.declare_vars *> get) mk_var2blockid

@[reducible] def ssa_valid_m := except_t format (reader_t var2blockid (state_t var_set id))

def ssa_valid_m.run {α} (a : ssa_valid_m α) (m : var2blockid) : except format α :=
run a m mk_var_set

/- Mark `x` as a variable defined in the current basic block. -/
def var.define (x : var) : ssa_valid_m unit :=
modify $ λ s, s.insert x

def arg.define (a : arg) : ssa_valid_m unit :=
a.n.define

/- Check whether `x` has been already defined in the current basic block or not. -/
def var.defined (x : var) : ssa_valid_m unit :=
do s ← get,
   if s.contains x then pure ()
   else throw ("undefined '" ++ to_fmt x ++ "'")

/- Given, x := phi ys,
   check whether every ys is declared at the var2blockid mapping,
   and update the set of already defined variables in the basic block with `x`. -/
def phi.valid_ssa (p : phi) : ssa_valid_m unit :=
p.decorate_error $
do m ← read,
   p.ys.mfor $ λ y, unless (m.contains y) $ throw ("undefined '" ++ to_fmt y ++ "'"),
   p.x.define

def instr.valid_ssa (ins : instr) : ssa_valid_m unit :=
ins.decorate_error $
match ins with
| (instr.assign x _ y)           := x.define *> y.defined
| (instr.assign_lit x _ _)       := x.define
| (instr.assign_unop x _ _ y)    := x.define *> y.defined
| (instr.assign_binop x _ _ y z) := x.define *> y.defined *> z.defined
| (instr.unop _ x)               := x.defined
| (instr.call x _ ys)            := x.define *> ys.mfor var.defined
| (instr.cnstr o _ _ _)          := o.define
| (instr.set o _ x)              := o.defined *> x.defined
| (instr.get x y _)              := x.define *> y.defined
| (instr.sset o _ x)             := o.defined *> x.defined
| (instr.sget x _ y _)           := x.define *> y.defined
| (instr.closure x _ ys)         := x.define *> ys.mfor var.defined
| (instr.apply x ys)             := x.define *> ys.mfor var.defined
| (instr.array a sz c)           := a.define *> sz.defined *> c.defined
| (instr.sarray x _ sz c)        := x.define *> sz.defined *> c.defined
| (instr.array_write a i v)      := a.defined *> i.defined *> v.defined

def terminator.valid_ssa (term : terminator) : ssa_valid_m unit :=
term.decorate_error $
match term with
| (terminator.ret y)      := y.defined
| (terminator.case x _)   := x.defined
| (terminator.jmp _)      := pure ()

def phi.predecessors (p : phi) : ssa_valid_m blockid_set :=
p.ys.mfoldl (λ s y,
  do m ← read,
     match m.find y with
     | some bid := if s.contains bid
                   then throw ("multiple predecessors at '" ++ to_fmt p ++ "'")
                   else pure $ s.insert bid
     | none   := throw ("undefined '" ++ to_fmt y ++ "' at '" ++ to_fmt p ++ "'"))
  mk_blockid_set

def phis.check_predecessors (ps : list phi) : ssa_valid_m unit :=
do ps.mfoldl (λ (os : option blockid_set) (p : phi),
     p.decorate_error $
     do s' ← p.predecessors,
        match os with
        | (some s) := if s.seteq s' then pure os
                      else throw ("missing predecessor '" ++ to_fmt p.x ++ "' at '" ++ to_fmt p ++ "'")
        | none      := pure (some s'))
     none,
   pure ()

def block.valid_ssa_core (b : block) : ssa_valid_m unit :=
b.decorate_error $
do phis.check_predecessors b.phis,
   b.phis.mfor phi.valid_ssa,
   b.instrs.mfor instr.valid_ssa,
   b.term.valid_ssa

/-
We first check whether every variable `x` was declared only once
and store the blockid where `x` is defined (action: `decl.declare_vars`).
Then, we check whether every used variable in basic block has been
defined before being used.
-/
def decl.valid_ssa (d : decl) : except format var2blockid :=
d.decorate_error $
do m ← d.var2blockid,
   match d with
   | decl.defn {args:=args, ..} (b::bs) :=
       (args.mfor arg.define *> block.valid_ssa_core b).run m
    *> (bs.mfor block.valid_ssa_core).run m
    *> pure m
   | _                   := pure m

/- Check blockids -/
@[reducible] def blockid_check_m :=
except_t format (state blockid_set)

def blockid_check_m.run {α} (a : blockid_check_m α) : except format α :=
run a mk_blockid_set

def block.declare (b : block) : blockid_check_m unit :=
do s ← get,
   if s.contains b.id then throw $ "block label '" ++ to_fmt b.id ++ "' has been used more than once"
   else put (s.insert b.id)

def blockid.defined (bid : blockid) : blockid_check_m unit :=
do s ← get,
   if s.contains bid then pure ()
   else throw $ "unknown basic block '" ++ to_fmt bid ++ "'"

def terminator.check_blockids (term : terminator) : blockid_check_m unit :=
term.decorate_error $
match term with
| (terminator.ret ys)      := pure ()
| (terminator.case _ bids) := bids.mfor blockid.defined
| (terminator.jmp bid)     := bid.defined

def block.check_blockids (b : block) : blockid_check_m unit :=
b.term.check_blockids

def decl.check_blockids : decl → blockid_check_m unit
| (decl.defn h bs) := h.decorate_error $ bs.mfor block.declare *> bs.mfor block.check_blockids
| _                := pure ()

def check_blockids (d : decl) : except format blockid_set :=
(d.check_blockids *> get).run

end ir
end lean
