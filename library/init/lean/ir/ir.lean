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
/-
The type `object` is a pointer to constructor/composite objects, arrays of objects, scalar arrays (`string` is a scalar array),
closures, big numbers (implemented using GMP), external objects or a tagged pointer.
Tagged pointers are used to represent small scalar values in polymorphic code.

The other types `bool/byte/uint16/uint32/uint64/usize/int16/int32/int64/float/double` are the usual unboxed scalar data.
We box values of type `bool/byte/uint16/uint32/int16/int32/float` are boxed (in 64-bit machines) as tagged pointers.
`usize/uint64/int64/double` are boxed by creating a composite object with a single field. -/
inductive type | bool | byte | uint16 | uint32 |
uint64 | usize | int16 | int32 | int64 | float | double | object

/- TEMPORARY HACK for defining (decidable_eq type) until we bootstrap new compiler -/
def type2id : type → nat
| type.bool   := 0  | type.byte   := 1
| type.uint16 := 2  | type.uint32 := 3  | type.uint64 := 4 | type.usize := 5
| type.int16  := 6  | type.int32  := 7  | type.int64  := 8
| type.float  := 9  | type.double := 10 | type.object := 11

def id2type : nat → type
| 0 := type.bool   | 1 := type.byte
| 2 := type.uint16 | 3 := type.uint32  | 4 := type.uint64 | 5 := type.usize
| 6 := type.int16  | 7 := type.int32   | 8 := type.int64
| 9 := type.float  | 10 := type.double | _       := type.object

theorem id2type_type2id_eq : ∀ (ty : type), id2type (type2id ty) = ty
| type.bool   := rfl  | type.byte   := rfl
| type.uint16 := rfl  | type.uint32 := rfl  | type.uint64 := rfl | type.usize := rfl
| type.int16  := rfl  | type.int32  := rfl  | type.int64  := rfl
| type.float  := rfl  | type.double := rfl  | type.object := rfl

instance type_has_dec_eq : decidable_eq type :=
λ t₁ t₂,
 if h : type2id t₁ = type2id t₂
 then is_true (id2type_type2id_eq t₁ ▸ id2type_type2id_eq t₂ ▸ h ▸ rfl)
 else is_false (λ h', absurd rfl (@eq.subst _ (λ t, ¬ type2id t = type2id t₂) _ _ h' h))
/- END of TEMPORARY HACK for (decidable_eq type) -/

/-- Operators for instructions of the form `x : t := op y`

- `x : t := not y`, if `t = bool`, then it is the logical negation.
Otherwise, it is bitwise negation if `t` is `uint32/uint64/usize`.

- `x : t := neg y`, arithmetical `-`. `t` is `int16/int32/int64/float/double/object`.
If `t` is `object`, the instruction is unspecified if `t` is not a big number.
When `t` is a big number, the operation will destructively update `y` if `RC = 1` and set `x` to `y`.
Otherwise, it decrements `RC(y)`, and allocates a new big number to store the result.

- `x : bool := is_scalar y`, set `x` to `tt` iff `y : object` is a tagged
pointer.

- `x : bool := is_shared y`, set `x` to `tt` iff `y : object` `RC(y)` is greater than 1.
The behavior is unspecified if `y` is a tagged pointer.

- `x : bool := is_null y`, set `x` to `tt` iff `y : object` is null.

- `x : t := cast y` is a scalar type casting operation. `t` and `typeof(y)` must not be
`object`.

- `x : object := box y` convert `y : t` where `t` is `int32/uint32` into a tagged
pointer. `y` must fit in 31bits (in 32-bit machines).

- `x : t := unbox y` convert `y : object` back into a scalar value. `t` is `int32/uint32`.
The behavior is unspecified if `y` is not a tagged pointer.

- `x : object := array_copy y` creates a copy of the array `y : object`.
The behavior is unspecified if `y` is not an array of objects.

- `x : object := sarray_copy y` creates a copy of the scalar array `y : object`.
The behavior is unspecified if `y` is not an array of scalar values.

- `x : usize := array_size y` stores the size of the array `y : object` into `x`.
The behavior is unspecified if `y` is not an array of objects.

- `x : usize : sarray_size y` stores the size of the scalar array `y : object` into `x`.
The behavior is unspecified if `y` is not an array of scalar values.

- `x : usize : string_len y` stores the length of the string `y : object` into `x`.
The length is the number of unicode scalar values.
The behavior is unspecified if `y` is not a string.
-/
inductive unop
| not | neg | is_scalar | is_shared | is_null | cast | box | unbox
| array_copy | sarray_copy | array_size | sarray_size | string_len

/-- Operators for instructions of the form `x : t := op y z` -/
inductive binop
| add | sub | mul | div | mod | shl | shr | and | or | xor
| le  | ge  | lt  | gt  | eq  | ne
| array_read -- (scalar) array read

/-- Operators for instructions of the form `op x` -/
inductive unins
| inc        -- increment reference counter
| dec        -- decrement reference counter
| decs       -- decrement reference counter of shared object
| free       -- free object memory, object must not be an external or big number
| dealloc    -- free object memory
| array_pop  -- array pop back
| sarray_pop -- scalar array pop back

inductive literal
| bool    : bool   → literal
| str     : string → literal
| num     : int    → literal  -- for uint32/uint64/int32/int64/byte/object literals
| float   : string → literal  -- for float/double literals

def tag     := uint16
def var     := name
def fnid    := name
def blockid := name

instance : has_coe string fnid :=
⟨mk_simple_name⟩

-- TODO: move collection declarations to another file
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
def fnid2string    := rbmap fnid string (<)
def fnid_set       := rbtree fnid (<)
def mk_var_set     : var_set     := mk_rbtree var (<)
def mk_blockid_set : blockid_set := mk_rbtree blockid (<)
def mk_var2blockid : var2blockid := mk_rbmap var blockid (<)
def mk_context     : context     := mk_rbmap var type (<)
def mk_fnid2string : fnid2string := mk_rbmap fnid string (<)
def mk_fnid_set    : fnid_set    := mk_rbtree fnid (<)

inductive instr
| lit     (x : var) (ty : type) (lit : literal)                 -- x : ty := lit
| unop    (x : var) (ty : type) (op : unop) (y : var)           -- x : ty := op y
| binop   (x : var) (ty : type) (op : binop) (y z : var)        -- x : ty := op y z
| call    (xs : list var) (f : fnid) (ys : list var)            -- Function call:  xs := f ys
/- Constructor objects -/
| cnstr   (o : var) (tag : tag) (nobjs : uint16) (ssz : usize)  -- Create constructor object
| set     (o : var) (i : uint16) (x : var)                      -- Set object field:          set o i x
| get     (x : var) (o : var) (i : uint16)                      -- Get object field:          x := get o i
| sset    (o : var) (d : usize) (v : var)                       -- Set scalar field:          sset o d v
| sget    (x : var) (ty : type) (o : var) (d : usize)           -- Get scalar field:          x : ty := sget o d
/- Closures -/
| closure (x : var) (f : fnid) (ys : list var)                  -- Create closure:            x := closure f ys
| apply   (x : var) (ys : list var)                             -- Apply closure:             x := apply ys
/- Arrays -/
| array   (a sz c : var)                                        -- Create array of objects with size `sz` and capacity `c`
| sarray  (a : var) (ty : type) (sz c : var)                    -- Create scalar array
| array_write (a i v : var)                                     -- (scalar) Array write      write a i v
| array_push  (a v : var)                                       -- (scalar) Array push back  push a v
-- TODO: add string_push and string_append
/- Unary instructions -/
| unary   (op : unins) (x : var)                                -- op x

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

instance : inhabited result :=
⟨⟨type.bool⟩⟩

/--
Header of function declarations.
If `is_const` is `tt` than it is a constant declaration.
The result of this kind of function (when `args = []`) is precomputed
during compilation unit initialization. -/
structure header :=
(name : fnid) (args : list arg) (return : list result) (is_const : bool)

inductive decl
| external (h : header)
| defn     (h : header) (bs : list block)

def decl.is_definition : decl → bool
| (decl.defn _ _) := tt
| _               := ff

def decl.header : decl → header
| (decl.external h) := h
| (decl.defn h _)   := h

def decl.name (d : decl) : name :=
d.header.name

def environment := fnid → option decl

end ir
end lean
