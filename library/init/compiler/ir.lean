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
def mk_var_set     := mk_rbtree var (<)
def mk_blockid_set := mk_rbtree blockid (<)
def var2blockid    := rbmap var blockid (<)
def mk_var2blockid := mk_rbmap var blockid (<)

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

def var.declare_at (b : blockid) (x : var) : ssa_check :=
do (m, s) ← get,
   if m.contains x then throw ("variable has already been defined '" ++ x ++ "'")
   else put (m.insert x b, s)

def instr.declare_vars_at (b : blockid) : instr → ssa_check
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

def phi.declare_at (b : blockid) : phi → ssa_check
| {x := x, ..} := x.declare_at b

def block.declare_vars : block → ssa_check
| {id := b, phis := ps, instrs := is, ..} :=
  ps.mmap' (phi.declare_at b) >>
  is.mmap' (instr.declare_vars_at b)

def arg.declare_at (b : blockid) : arg → ssa_check
| {n := x, ..} := x.declare_at b

/- Collect where each variable is declared, and
   check whether each variable was declared at most once. -/
def decl.declare_vars : decl → ssa_check
| {as := as, bs := b::bs, ..} :=
  /- We assume that arguments are declared in the first basic block.
     TODO: check whether this assumption matches LLVM or not -/
  as.mmap' (arg.declare_at b.id) >>
  b.declare_vars >>
  bs.mmap' block.declare_vars
| _ := throw "declaration must have at least one block"

/- Generate the mapping from variable to blockid for the given declaration.
   This function assumes `d` is in SSA. -/
def decl.var2blockid (d : decl) : var2blockid :=
let (_, (m, _)) := d.declare_vars.run.run (mk_var2blockid, mk_var_set) in
m

/- Given, x := phi ys,
   check whether every ys is declared at the var2blockid mapping,
   and update the set of already defined variables in the basic block with `x`.

   TODO: check whether the SSA validation rules here match the ones used in LLVM. -/
def phi.valid_ssa : phi → ssa_check
| {x := x, ys := ys, ..} := do
  (m, s) ← get,
  ys.mmap' (λ y, if m.contains y then return ()
                 else throw ("undefined '" ++ y ++ "'")),
  put (m, s.insert x)

/- Check whether `x` has been already defined in the current basic block or not. -/
def var.defined (x : var) : ssa_check :=
do (_, s) ← get,
   if s.contains x then return ()
   else throw ("undefined variable '" ++ x ++ "'")

/- Mark `x` as a variable defined in the current basic block. -/
def var.define (x : var) : ssa_check :=
do (m, s) ← get, put (m, s.insert x)

def instr.valid_ssa : instr → ssa_check
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

def terminator.valid_ssa : terminator → ssa_check
| (terminator.ret ys)     := ys.mmap' var.defined
| (terminator.case x _)   := x.defined
| (terminator.jmp _)      := return ()

def block.valid_ssa : block → ssa_check
| {phis := ps, instrs := is, term := r, ..} :=
  do (m, s) ← get,
     put (m, mk_var_set), -- reset set of variables defined in the current block
     ps.mmap' phi.valid_ssa,
     is.mmap' instr.valid_ssa,
     r.valid_ssa

/-
We first check whether every variable `x` was declared only once
and store the blockid where `x` is defined (action: `decl.declare_vars`).
Then, we check whether every used variable in basic block has been
defined before being used.
-/
def decl.valid_ssa : decl → ssa_check
| d@{as := as, bs := bs, ..} :=
  d.declare_vars >> bs.mmap' block.valid_ssa

def valid_ssa (d : decl) : bool :=
let (e, _) := d.valid_ssa.run.run (mk_var2blockid, mk_var_set)
in  e.to_bool

/- Check blockids -/
@[reducible] def blockid_check : Type :=
except_t string (state blockid_set) unit

def block.declare : block → blockid_check
| {id := id, ..} :=
  do s ← get,
     if s.contains id then throw ("blockid '" ++ id ++ "' has already been used")
     else put (s.insert id)

def blockid.defined (bid : blockid) : blockid_check :=
do s ← get,
   if s.contains bid then return ()
   else throw ("unknown blockid '" ++ bid ++ "'")

def terminator.check_blockids : terminator → blockid_check
| (terminator.ret ys)      := return ()
| (terminator.case _ bids) := bids.mmap' blockid.defined
| (terminator.jmp bid)     := bid.defined

def block.check_blockids : block → blockid_check
| {term := r, ..} := r.check_blockids

def decl.check_blockids : decl → blockid_check
| {bs := bs, ..} :=
  bs.mmap' block.declare >> bs.mmap' block.check_blockids

def check_blockids (d : decl) : bool :=
let (e, _) := d.check_blockids.run.run mk_blockid_set
in  e.to_bool

/-
TODO: type inference
-/

end ir
end lean
