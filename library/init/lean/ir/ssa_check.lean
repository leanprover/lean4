/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir

namespace lean
namespace ir
/-
SSA validator
-/
inductive ssa_error
| already_defined (b : blockid) (x : var)                         -- variable `x` has already been defined at basic block `b`
| undefined (b : blockid) (x : var)                               -- undefined variable `x` at basic block `b`
| phi_multiple_entries (b : blockid) (x : var) (pred : blockid)   -- `x := phi y_1 ... y_n` at basic block `b`, where there are `y_i` and `y_j` defined in the same basic block `pred`
| phi_missing_predecessor (b : blockid) (x : var)                 -- `x := phi ys` has a missing predecessor at basic block `b`
| no_block

@[reducible] def ssa_decl_m := except_t ssa_error (state_t var2blockid id)

def var.declare_at (b : blockid) (x : var) : ssa_decl_m unit :=
do m ← get,
   if m.contains x then throw (ssa_error.already_defined b x)
   else put (m.insert x b)

def instr.declare_vars_at (b : blockid) : instr → ssa_decl_m unit
| (instr.lit x _ _)       := x.declare_at b
| (instr.unop x _ _ _)    := x.declare_at b
| (instr.binop x _ _ _ _) := x.declare_at b
| (instr.call xs _ _)     := xs.mmap' (var.declare_at b)
| (instr.cnstr o _ _ _)   := o.declare_at b
| (instr.set o _ _)       := o.declare_at b
| (instr.get x _ _)       := x.declare_at b
| (instr.sset o _ _)      := o.declare_at b
| (instr.sget x _ _ _)    := x.declare_at b
| (instr.closure x _ _)   := x.declare_at b
| (instr.apply x _)       := x.declare_at b
| (instr.array a _ _)     := a.declare_at b
| (instr.read x _ _)      := x.declare_at b
| (instr.sarray x _ _ _)  := x.declare_at b
| (instr.sread x _ _ _)   := x.declare_at b
| _                       := return ()

def phi.declare_at (b : blockid) : phi → ssa_decl_m unit
| {x := x, ..} := x.declare_at b

def block.declare_vars : block → ssa_decl_m unit
| {id := b, phis := ps, instrs := is, ..} :=
  ps.mmap' (phi.declare_at b) >>
  is.mmap' (instr.declare_vars_at b)

def arg.declare_at (b : blockid) : arg → ssa_decl_m unit
| {n := x, ..} := x.declare_at b

/- Collect where each variable is declared, and
   check whether each variable was declared at most once. -/
def decl.declare_vars : decl → ssa_decl_m unit
| (decl.defn {args := as, ..} (b::bs)) :=
  /- We assume that arguments are declared in the first basic block.
     TODO: check whether this assumption matches LLVM or not -/
  as.mmap' (arg.declare_at b.id) >>
  b.declare_vars >>
  bs.mmap' block.declare_vars
| (decl.defn _  []) := throw ssa_error.no_block
| _                 := return ()

/- Generate the mapping from variable to blockid for the given declaration.
   This function assumes `d` is in SSA. -/
def decl.var2blockid (d : decl) : except_t ssa_error id var2blockid :=
run_state (d.declare_vars >> get) mk_var2blockid

@[reducible] def ssa_valid_m := except_t ssa_error (reader_t (var2blockid × block) (state_t var_set id))

def read_var2blockid : ssa_valid_m var2blockid :=
prod.fst <$> read

def read_block : ssa_valid_m block :=
prod.snd <$> read

/- Mark `x` as a variable defined in the current basic block. -/
def var.define (x : var) : ssa_valid_m unit :=
modify $ λ s, s.insert x

/- Check whether `x` has been already defined in the current basic block or not. -/
def var.defined (x : var) : ssa_valid_m unit :=
do s ← get,
   if s.contains x then return ()
   else do b ← read_block,
           throw (ssa_error.undefined b.id x)

/- Given, x := phi ys,
   check whether every ys is declared at the var2blockid mapping,
   and update the set of already defined variables in the basic block with `x`. -/
def phi.valid_ssa (p : phi) : ssa_valid_m unit :=
do m ← read_var2blockid,
   p.ys.mmap' (λ y, if m.contains y then return ()
                 else do b ← read_block,
                         throw (ssa_error.undefined b.id y)),
   p.x.define

def instr.valid_ssa : instr → ssa_valid_m unit
| (instr.lit x _ _)       := x.define
| (instr.unop x _ _ y)    := x.define >> y.defined
| (instr.binop x _ _ y z) := x.define >> y.defined >> z.defined
| (instr.call xs _ ys)    := xs.mmap' var.define >> ys.mmap' var.defined
| (instr.cnstr o _ _ _)   := o.define
| (instr.set o _ x)       := o.defined >> x.defined
| (instr.get x y _)       := x.define >> y.defined
| (instr.sset o _ x)      := o.defined >> x.defined
| (instr.sget x _ y _)    := x.define >> y.defined
| (instr.closure x _ ys)  := x.define >> ys.mmap' var.defined
| (instr.apply x ys)      := x.define >> ys.mmap' var.defined
| (instr.array a sz c)    := a.define >> sz.defined >> c.defined
| (instr.write a i v)     := a.defined >> i.defined >> v.defined
| (instr.read x a i)      := x.define >> a.defined >> i.defined
| (instr.sarray x _ sz c) := x.define >> sz.defined >> c.defined
| (instr.swrite a i v)    := a.defined >> i.defined >> v.defined
| (instr.sread x _ a i)   := x.define >> a.defined >> i.defined
| (instr.inc x)           := x.defined
| (instr.decs x)          := x.defined
| (instr.free x)          := x.defined
| (instr.dec x)           := x.defined

def terminator.valid_ssa : terminator → ssa_valid_m unit
| (terminator.ret ys)     := ys.mmap' var.defined
| (terminator.case x _)   := x.defined
| (terminator.jmp _)      := return ()

def phi.predecessors (p : phi) : ssa_valid_m blockid_set :=
p.ys.mfoldl (λ s y,
  do m ← read_var2blockid,
     match m.find y with
     | some bid := if s.contains bid
                   then do b ← read_block,
                           throw (ssa_error.phi_multiple_entries b.id p.x bid)
                   else return $ (s.insert bid)
     | none   := do b ← read_block, throw (ssa_error.undefined b.id y))
  mk_blockid_set

def phis.check_predecessors (ps : list phi) : ssa_valid_m unit :=
do ps.mfoldl (λ (os : option blockid_set) (p : phi),
     do s' ← p.predecessors,
        match os with
        | (some s) := if s.seteq s' then return os
                      else do b ← read_block,
                              throw (ssa_error.phi_missing_predecessor b.id p.x)
        | none      := return (some s'))
     none,
   return ()

def block.valid_ssa_core : ssa_valid_m unit :=
do b ← read_block,
   phis.check_predecessors b.phis,
   b.phis.mmap' phi.valid_ssa,
   b.instrs.mmap' instr.valid_ssa,
   b.term.valid_ssa

def block.valid_ssa : except_t ssa_error (reader_t (var2blockid × block) id) unit :=
run_state block.valid_ssa_core mk_var_set

/-
We first check whether every variable `x` was declared only once
and store the blockid where `x` is defined (action: `decl.declare_vars`).
Then, we check whether every used variable in basic block has been
defined before being used.
-/
def decl.valid_ssa (d : decl) : except_t ssa_error id var2blockid :=
do m ← d.var2blockid,
   match d with
   | decl.defn _ bs := do
      bs.mmap' (λ b : block, run_reader block.valid_ssa (m, b)),
      return m
   | _ := return m

/- Check blockids -/
inductive blockid_error
| already_used (bid : blockid)
| unknown (bid : blockid)

@[reducible] def blockid_check_m :=
except_t blockid_error (state blockid_set)

def block.declare (b : block) : blockid_check_m unit :=
do s ← get,
   if s.contains b.id then throw $ blockid_error.already_used b.id
   else put (s.insert b.id)

def blockid.defined (bid : blockid) : blockid_check_m unit :=
do s ← get,
   if s.contains bid then return ()
   else throw $ blockid_error.unknown bid

def terminator.check_blockids : terminator → blockid_check_m unit
| (terminator.ret ys)      := return ()
| (terminator.case _ bids) := bids.mmap' blockid.defined
| (terminator.jmp bid)     := bid.defined

def block.check_blockids (b : block) : blockid_check_m unit :=
b.term.check_blockids

def decl.check_blockids : decl → blockid_check_m unit
| (decl.defn _ bs) := bs.mmap' block.declare >> bs.mmap' block.check_blockids
| _                := return ()

def check_blockids (d : decl) : except_t blockid_error id blockid_set :=
run_state (d.check_blockids >> get) mk_blockid_set

/-
TODO: type inference
-/

end ir
end lean
