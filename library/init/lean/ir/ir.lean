/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbmap init.data.int init.control.state init.control.except init.control.combinators
import init.lean.name

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
| add | sub | mul | div | mod | shl | shr | ashr | and | or | xor
| le  | ge  | lt  | gt  | eq  | ne

inductive literal
| bool    : bool   → literal
| str     : string → literal
| num     : int    → literal  -- for uint32/uint64/int32/int64/byte literals
| float   : string → literal  -- for float/double literals

def tag     := uint16
def var     := name
def fnid    := name
def blockid := name

instance var_has_lt : has_lt var := (name.has_lt_quick : has_lt name)
instance blockid_has_lt : has_lt blockid := (name.has_lt_quick : has_lt name)
instance fnid_has_lt : has_lt fnid := (name.has_lt_quick : has_lt name)

instance var_has_dec_eq : decidable_eq var := infer_instance_as (decidable_eq name)
instance blockid_has_dec_eq : decidable_eq blockid := infer_instance_as (decidable_eq name)
instance fnid_has_dec_eq : decidable_eq fnid := infer_instance_as (decidable_eq name)

instance var_hashable : hashable var := infer_instance_as (hashable name)
instance blockid_hashable : hashable blockid := infer_instance_as (hashable name)
instance fnid_hashable : hashable fnid := infer_instance_as (hashable name)

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
| call    (xs : list var) (f : fnid) (ys : list var)         -- Function call:  xs := f ys
/- Constructor objects -/
| cnstr   (o : var) (tag : tag) (nobjs ssz : uint16)         -- Create constructor object
| set     (o : var) (i : uint16) (x : var)                   -- Set object field:          set o i x
| get     (x : var) (o : var) (i : uint16)                   -- Get object field:          x := get o i
| sset    (o : var) (d : uint16) (v : var)                   -- Set scalar field:          sset o d v
| sget    (x : var) (ty : type) (o : var) (d : uint16)       -- Get scalar field:          x : ty := sget o d
/- Closures -/
| closure (x : var) (f : fnid) (ys : list var)               -- Create closure:            x := closure f ys
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
| free    (x : var)
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

structure header :=
(n : fnid) (args : list arg) (return : list result)

inductive decl
| external (h : header)
| defn     (h : header) (bs : list block)

end ir
end lean
