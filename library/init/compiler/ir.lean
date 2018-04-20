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

def var_set     := rbtree var (<)
def blockid_set := rbtree blockid (<)
def context     := rbmap var type (<)
def mk_var_set  := mk_rbtree var (<)

inductive instr
| lit     (x : var) (ty : type) (lit : literal)              -- x : ty := lit
| cast    (x : var) (ty : type) (y : var)                    -- x : ty := y
| unop    (x : var) (ty : type) (op : unop) (y : var)        -- x : ty := op y
| binop   (x : var) (ty : type) (op : binop) (y z : var)     -- x : ty := op y z
| call    (xs : list var) (f : fid) (ys : list var)          -- Function call:  xs := f ys
| phi     (x : var) (ys : list (var × blockid))              -- var := phi (var, blockid) ... (var, blockid)
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

inductive terminator
| ret  (ys : list var)
| case (x : var) (bs : list blockid)
| jmp  (b : blockid)

structure block :=
(id : blockid) (instrs : list instr) (term : terminator)

structure arg :=
(n : var) (ty : type)

structure result :=
(ty : type)

structure decl :=
(n : fid) (as : list arg) (rs : list result) (bs : list block)

/-
Check whether every variable is defined only once.
-/
section ssa_validation

@[reducible] def ssa_check : Type :=
except_t unit (state var_set) unit

def var.defined (x : var) : ssa_check :=
do s ← get,
   if s.contains x then return ()
   else throw ()

def var.not_defined (x : var) : ssa_check :=
do s ← get,
   if s.contains x then throw ()
   else put (s.insert x)

def instr.valid_ssa : instr → ssa_check
| (instr.lit x _ _)       := x.not_defined
| (instr.cast x _ y)      := x.not_defined >> y.defined
| (instr.unop x _ _ y)    := x.not_defined >> y.defined
| (instr.binop x _ _ y z) := x.not_defined >> y.defined >> z.defined
| (instr.call xs _ ys)    := xs.mmap' var.not_defined >> ys.mmap' var.defined
| (instr.phi x ps)        := x.not_defined >> ps.mmap' (λ ⟨y, _⟩, y.defined)
| (instr.cnstr o _ _ _)   := o.not_defined
| (instr.set o _ x)       := o.defined >> x.defined
| (instr.get x y _)       := x.not_defined >> y.defined
| (instr.sets o _ x)      := o.defined >> x.defined
| (instr.gets x _ y _)    := x.not_defined >> y.defined
| (instr.closure x _ ys)  := x.not_defined >> ys.mmap' var.defined
| (instr.apply x ys)      := x.not_defined >> ys.mmap' var.defined
| (instr.array a sz c)    := a.not_defined >> sz.defined >> c.defined
| (instr.write a i v)     := a.defined >> i.defined >> v.defined
| (instr.read x a i)      := x.not_defined >> a.defined >> i.defined
| (instr.sarray x _ sz c) := x.not_defined >> sz.defined >> c.defined
| (instr.swrite a i v)    := a.defined >> i.defined >> v.defined
| (instr.sread x _ a i)   := x.not_defined >> a.defined >> i.defined
| (instr.inc x)           := x.defined
| (instr.decs x)          := x.defined
| (instr.dealloc x)       := x.defined
| (instr.dec x)           := x.defined

def arg.valid_ssa : arg → ssa_check
| {n := x, ..} := x.not_defined

def block.valid_ssa : block → ssa_check
| {instrs := is, ..} := is.mmap' instr.valid_ssa

def decl.valid_ssa : decl → ssa_check
| {as := as, bs := bs, ..} :=
  as.mmap' arg.valid_ssa >> bs.mmap' block.valid_ssa

def valid_ssa (d : decl) : bool :=
let (e, _) := d.valid_ssa.run.run mk_var_set
in  e.to_bool

end ssa_validation

/-
TODO:
- blockid validation
- type checker
-/


end ir
end lean
