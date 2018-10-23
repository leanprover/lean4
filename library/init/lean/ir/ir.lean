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

/-- Operators for instructions of the form `x : t := op y`

- `x : t := not y`, if `t = bool`, then it is the logical negation.
Otherwise, it is bitwise negation if `t` is `uint32/uint64/usize`.

- `x : t := neg y`, arithmetical `-`. `t` is `int16/int32/int64/float/double`.

- `x : object := ineg y`, integer `-`.

- `x : object := nat2int y`, convert a natural (big) number into an integer (big) number.

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
Remark: `sarray_copy` can be used to copy strings.

- `x : usize := array_size y` stores the size of the array `y : object` into `x`.
The behavior is unspecified if `y` is not an array of objects.

- `x : usize := sarray_size y` stores the size of the scalar array `y : object` into `x`.
The behavior is unspecified if `y` is not an array of scalar values.

- `x : usize := string_len y` stores the length of the string `y : object` into `x`.
The length is the number of unicode scalar values.
The behavior is unspecified if `y` is not a string.

- `x : object := succ y` natural number successor.

- `x : uint32 := tag_ref y` return the tag of the (constructor) object `y`. `y` must not be
  a tagged pointer.

- `x : uint32 := tag y` return the tag of the (constructor) object `y` OR tagged pointer.
-/
inductive assign_unop
| not | neg | ineg | nat2int | is_scalar | is_shared | is_null | cast | box | unbox
| array_copy | sarray_copy | array_size | sarray_size | string_len
| succ | tag | tag_ref

/-- Operators for instructions of the form `x : t := op y z`

- `x : t := add y z`: addition. Remark: `t ≠ bool`.
When `t = object`, i.e., `t` is big number or tagged pointer, a new big number may be allocated
if the result does not fit in a tagged pointer.

- `x : t := sub y z`: subtraction. Remark: `t ≠ bool`. See `add` for big number case.

- `x : t := mul y z`: multiplication. Remark: `t ≠ bool`. See `add` for big number case.

- `x : t := div y z`: division. Remark: `t ≠ bool`. See `add` for big number case.

- `x : t := mod y z`: modulo. Remark: `t ≠ bool`, `t ≠ float` and `t ≠ double`. See `add` for big number case.

- `x : object := iadd y z`: (big) integer addition.

- `x : object := isub y z`: (big) integer subtraction.

- `x : object := imul y z`: (big) integer multiplication.

- `x : object := idiv y z`: (big) integer division.

- `x : object := imod y z`: (big) integer modulo.

- `x : t := shl y z`: bit shift left. Remark: `t ≠ bool`, `t ≠ float`, `t ≠ double` and `t ≠ object`.

- `x : t := shr y z`: bit shift right. Remark: `t ≠ bool`, `t ≠ float`, `t ≠ double` and `t ≠ object`.
If `t` is `int16`, `int32` or `int64`, it is an arithmetical bit shift.

- `x : t := and y z`: if `t = bool`, then it is the logical and. Otherwise, it is the bitwise and.
Remark: `t ≠ bool`, `t ≠ float`, `t ≠ double` and `t ≠ object`.

- `x : t := or y z`: if `t = bool`, then it is the logical or. Otherwise, it is the bitwise or.
Remark: `t ≠ bool`, `t ≠ float`, `t ≠ double` and `t ≠ object`.

- `x : t := xor y z`: if `t = bool`, then it is the logical xor. Otherwise, it is the bitwise xor.
Remark: `t ≠ bool`, `t ≠ float`, `t ≠ double` and `t ≠ object`.

- `x : bool := le y z`: less than or equal to. Remark: `t ≠ bool`.
If `y` and `z` are `object`, then they must be big numbers.

- `x : bool := lt y z`: less than. Remark: `t ≠ bool`.
If `y` and `z` are `object`, then they must be big numbers.

- `x : bool := eq y z`: equality test. If `y` and `z` are `object`, then they must be big numbers.

- `x : bool := ne y z`: disequality test. If `y` and `z` are `object`, then they must be big numbers.

- `x : bool := ile y z`: (big) integer less than or equal to. `y` and `z` have type `object`.

- `x : bool := ilt y z`: (big) integer less than. `y` and `z` have type `object`.

- `x : bool := ieq y z`: (big) integer equality. `y` and `z` have type `object`.

- `x : bool := ine y z`: (big) integer disequality. `y` and `z` have type `object`.

- `x : t := array_read a i`: Read position `i` of the array `a`. `a` must be an (array) `object`.
If `a` is a scalar array, then `t ≠ object`. If `a` is an (non-scalar) array, then `t = object`.

- `r : object := array_push a x`: push element `x` in the end of array `a`. `x` must have type `object`, `RC(x) = 1`, and it must
be an array. If `x` has a scalar type, then `a` is an array of scalar. Otherwise, it is an array of objects.
Remark: if `a` has space for the new element, then `r` is set to `a`. Otherwise, a new array object is allocated, set to `r`,
and `a` is deleted.

- `r : object := string_push s c`: push character `c` in the end of string `s`. `s` must have type `object`, and `RC(s) = 1`.
be a string.
Remark: if `s` has space for the new element, then `r` is set to `s`. Otherwise, a new string is allocated, set to `r`,
and `s` is deleted.

- `r : object : string_append s₁ s₂`: append string `s₂` in the end of string `s₁`. `s₁` must have type `object`, and `RC(s₁) = 1`.
Remark: if `s₁` has space for all `s₂` characters, then `r` is set to `s₁`. Otherwise, a new string is allocated, set to `r`,
and `s₁` is deleted.

Remark: in the future we may add instructions for performing updates destructively on big numbers. Example:
`add_acc x y` would be `x += y`, and require `RC(x) = 1`. -/
inductive assign_binop
| add  | sub  | mul  | div  | mod
| iadd | isub | imul | idiv | imod
| shl  | shr  | and  | or   | xor
| le   | lt   | eq   | ne
| ile  | ilt  | ieq  | ine
| array_read | array_push | string_push | string_append

/-- Operators for instructions of the form `op x`

- `inc_ref x`: increment `RC(x)`, `x` must have type `object`, and it must not be a tagged pointer.

- `dec_ref x`: decrement `RC(x)`, `x` must have type `object`, and it must not be a tagged pointer.
If `RC(x)` becomes zero, then `x` is deleted.

- `dec_sref x`: decrement `RC(x)`, `x` must have type `object`, `RC(x) > 1`, and it must not be a tagged pointer.
That is, `x` must be a shared object.

- `inc x`: increment `RC(x)` IF `x` is not a tagged pointer. `x` must have type `object`.

- `dec x`: decrement `RC(x)` IF `x` is not a tagged pointer.  `x` must have type `object`.

- `free x`: free `x`'s memory. `x` must have type `object`, it must not be a tagged pointer,
and it must not be an external or big number.

- `dealloc x`: finalize `x` and free `x`'s memory. `x` must have type `object`, and it must not be a tagged pointer.

- `array_pop x`: remove the last element of array `x`. `x` must have type `object`, `RC(x) = 1`, and it must
be an array of objects.

- `sarray_pop x`: remove the last element of array `x`. `x` must have type `object`, `RC(x) = 1`, and it must
be an array of scalar values. -/
inductive unop
| inc_ref | dec_ref | dec_sref | inc | dec
| free | dealloc
| array_pop | sarray_pop

inductive literal
| bool    : bool   → literal
| str     : string → literal
| num     : int    → literal  -- for uint32/uint64/int32/int64/byte/object literals
| float   : string → literal  -- for float/double literals

def tag     := uint16
def var     := name
def fnid    := name
def blockid := name

/- IR Instructions -/
inductive instr
| assign       (x : var) (ty : type) (y : var)                       -- x : ty := y
| assign_lit   (x : var) (ty : type) (lit : literal)                 -- x : ty := lit
| assign_unop  (x : var) (ty : type) (op : assign_unop) (y : var)    -- x : ty := op y
| assign_binop (x : var) (ty : type) (op : assign_binop) (y z : var) -- x : ty := op y z
| unop         (op : unop) (x : var)                                 -- op x
| call         (x : var) (f : fnid) (ys : list var)                  -- Function call:  x := f ys
/- Constructor objects -/
| cnstr   (o : var) (tag : tag) (nobjs : uint16) (ssz : usize)       -- Create constructor object
| set     (o : var) (i : uint16) (x : var)                           -- Set object field:          set o i x
| get     (x : var) (o : var) (i : uint16)                           -- Get object field:          x := get o i
| sset    (o : var) (d : usize) (v : var)                            -- Set scalar field:          sset o d v
| sget    (x : var) (ty : type) (o : var) (d : usize)                -- Get scalar field:          x : ty := sget o d
/- Closures -/
| closure (x : var) (f : fnid) (ys : list var)                       -- Create closure:            x := closure f ys
| apply   (x : var) (ys : list var)                                  -- Apply closure:             x := apply ys
/- Arrays -/
| array   (a sz c : var)                                             -- Create array of objects with size `sz` and capacity `c`
| sarray  (a : var) (ty : type) (sz c : var)                         -- Create scalar array
| array_write (a i v : var)                                          -- (scalar) Array write      write a i v

structure phi :=
(x : var) (ty : type) (ys : list var)

inductive terminator
| ret  (y : var)
| case (x : var) (bs : list blockid)
| jmp  (b : blockid)

structure block :=
(id : blockid) (phis : list phi) (instrs : list instr) (term : terminator)

structure arg :=
(n : var) (ty : type)

structure result :=
(ty : type)

/--
Header of function declarations.
If `is_const` is `tt` than it is a constant declaration.
The result of this kind of function (when `args = []`) is precomputed
during compilation unit initialization. -/
structure header :=
(name : fnid) (args : list arg) (return : result) (is_const : bool)

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
