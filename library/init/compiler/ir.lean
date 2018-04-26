/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbmap init.data.int init.category.state init.category.except init.category.combinators

/-
Missing
- float/double literals are strings since we did not define them in Lean
- borrowed annotations
-/

namespace lean
namespace ir

inductive type
| bool | byte | uint16 | uint32 | uint64 | int16 | int32 | int64 | float | double | object

inductive unop
| not | neg | scalar | shared
| unbox | box
| copy_array | copy_sarray

inductive binop
| add | sub | mul | div | mod | shl | shr | ashr | band | bor | bxor
| le  | ge  | lt  | gt  | eq  | ne

inductive literal
| bool    : bool   → literal
| str     : string → literal
| num     : int    → literal  -- for uint32/uint64/int32/int64/byte literals
| float   : string → literal  -- for float/double literals

def tag     := uint16
def var     := string
def fid     := string
def blockid := string

instance var_has_lt : has_lt var :=
show has_lt string, from infer_instance

instance blockid_has_lt : has_lt blockid :=
show has_lt string, from infer_instance

def var_set        := rbtree var (<)
def blockid_set    := rbtree blockid (<)
def context        := rbmap var type (<)
def var2blockid    := rbmap var blockid (<)
def mk_var_set     : var_set     := mk_rbtree var (<)
def mk_blockid_set : blockid_set := mk_rbtree blockid (<)
def mk_var2blockid : var2blockid := mk_rbmap var blockid (<)

inductive instr
| lit     (x : var) (ty : type) (lit : literal)              -- x : ty := lit
| cast    (x : var) (ty : type) (y : var)                    -- x : ty := y
| unop    (x : var) (ty : type) (op : unop) (y : var)        -- x : ty := op y
| binop   (x : var) (ty : type) (op : binop) (y z : var)     -- x : ty := op y z
| call    (xs : list var) (f : fid) (ys : list var)          -- Function call:  xs := f ys
/- Constructor objects -/
| cnstr   (o : var) (tag : tag) (nobjs ssz : uint16)         -- Create constructor object
| set     (o : var) (i : uint16) (x : var)                   -- Set object field:          set o i x
| get     (x : var) (o : var) (i : uint16)                   -- Get object field:          x := get o i
| sets    (o : var) (d : uint16) (v : var)                   -- Set scalar field:          sets o d v
| gets    (x : var) (ty : type) (o : var) (d : uint16)       -- Get scalar field:          x : ty := gets o d
/- Closures -/
| closure (x : var) (f : fid) (ys : list var)                -- Create closure:            x := closure f ys
| apply   (x : var) (ys : list var)                          -- Apply closure:             x := apply ys
/- Array of objects -/
| array   (a sz c : var)                                     -- Create array of objects with size `sz` and capacity `c`
| write   (a i v : var)                                      -- Array write                write a i v
| read    (x a i : var)                                      -- Array read                 x := a[i]
/- Scalar arrays -/
| sarray  (a : var) (ty : type) (sz c : var)                 -- Create scalar array
| swrite  (a i v : var)                                      -- Scalar array write         swrite a i v
| sread   (x : var) (ty : type) (a i : var)                  -- Scalar array read          x : type := a[i]
/- Reference counting -/
| inc     (x : var)                                          -- inc var
| decs    (x : var)                                          -- decrement RC of shared object
| dealloc (x : var)
| dec     (x : var)                                          -- Remark: can be defined using `decs`, `dealloc` and `shared`

structure phi :=
(x : var) (ty : type) (ys : list var)

inductive terminator
| ret  (ys : list var)
| case (x : var) (bs : list blockid)
| jmp  (b : blockid)

structure block :=
(id : blockid) (phis : list phi) (instrs : list instr) (term : terminator)

structure arg :=
(n : var) (ty : type)

structure result :=
(ty : type)

structure decl :=
(n : fid) (as : list arg) (rs : list result) (bs : list block)

/-
SSA validator
-/
@[reducible] def ssa_check : Type :=
except_t string (state (var2blockid × var_set)) unit

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
| (instr.cast x _ _)      := x.declare_at b
| (instr.unop x _ _ _)    := x.declare_at b
| (instr.binop x _ _ _ _) := x.declare_at b
| (instr.call xs _ _)     := xs.mmap' (var.declare_at b)
| (instr.cnstr o _ _ _)   := o.declare_at b
| (instr.set o _ _)       := o.declare_at b
| (instr.get x _ _)       := x.declare_at b
| (instr.sets o _ _)      := o.declare_at b
| (instr.gets x _ _ _)    := x.declare_at b
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
| {as := as, bs := b::bs, ..} :=
  /- We assume that arguments are declared in the first basic block.
     TODO: check whether this assumption matches LLVM or not -/
  as.mmap' (arg.declare_at b.id) >>
  b.declare_vars >>
  bs.mmap' block.declare_vars
| _ := throw ssa_error.no_block

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
| (instr.cast x _ y)      := x.define >> y.defined
| (instr.unop x _ _ y)    := x.define >> y.defined
| (instr.binop x _ _ y z) := x.define >> y.defined >> z.defined
| (instr.call xs _ ys)    := xs.mmap' var.define >> ys.mmap' var.defined
| (instr.cnstr o _ _ _)   := o.define
| (instr.set o _ x)       := o.defined >> x.defined
| (instr.get x y _)       := x.define >> y.defined
| (instr.sets o _ x)      := o.defined >> x.defined
| (instr.gets x _ y _)    := x.define >> y.defined
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
| (instr.dealloc x)       := x.defined
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
     | none   := do b ← read_block, throw (ssa_error.undefined b.id y)
     end)
  mk_blockid_set

def phis.check_predecessors (ps : list phi) : ssa_valid_m unit :=
do ps.mfoldl (λ (os : option blockid_set) (p : phi),
     do s' ← p.predecessors,
        match os with
        | (some s) := if s.seteq s' then return os
                      else do b ← read_block,
                              throw (ssa_error.phi_missing_predecessor b.id p.x)
        | none      := return (some s')
     end) none,
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
   d.bs.mmap' (λ b : block, run_reader block.valid_ssa (m, b)),
   return m

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

def decl.check_blockids (d : decl) : blockid_check_m unit :=
d.bs.mmap' block.declare >> d.bs.mmap' block.check_blockids

def check_blockids (d : decl) : except_t blockid_error id blockid_set :=
run_state (d.check_blockids >> get) mk_blockid_set

/-
TODO: type inference
-/

end ir
end lean
