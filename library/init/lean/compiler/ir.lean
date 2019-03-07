/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.name init.lean.kvmap
prelude

/-
Implements (extended) λ_pure and λ_RC proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λ_pure code. That is,
then transformed using the procedures described in the paper above.
-/
namespace lean
namespace ir

/- Variable identifier -/
abbreviation varid := name
/- Function identifier -/
abbreviation fid := name
/- Join point identifier -/
abbreviation jpid := name

/- Low level IR types. Most are self explanatory.

   - `usize` represents the C++ `size_t` type. We have it here
      because it is 32-bit in 32-bit machines, and 64-bit in 64-bit machines,
      and we want the C++ backend for our compiler to generate platform independent code.

   - `irrelevant` for Lean types, propositions and proofs.

   - `object` a pointer to a value in the heap.

   - `tobject` a pointer to a value in the heap or tagged pointer
      (i.e., the least significant bit is 1) storing a scalar value.

Remark: the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.

Remark: the Lean runtime assumes that sizeof(void*) == sizeof(size_t).
Lean cannot be compiled on old platforms where this is not true. -/
inductive type
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject

def type.beq : type → type → bool
| type.float      type.float      := tt
| type.uint8      type.uint8      := tt
| type.uint16     type.uint16     := tt
| type.uint32     type.uint32     := tt
| type.uint64     type.uint64     := tt
| type.usize      type.usize      := tt
| type.irrelevant type.irrelevant := tt
| type.object     type.object     := tt
| type.tobject    type.tobject    := tt
| _               _               := ff

instance type.has_beq : has_beq type := ⟨type.beq⟩

/- Arguments to applications, constructors, etc.
   We use `irrelevant` for Lean types, propositions and proofs that have been erased.
   Recall that for a function `f`, we also generate `f._rarg` which does not take
   `irrelevant` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive arg
| var (id : varid)
| irrelevant

inductive litval
| num (v : nat)
| str (v : string)

def litval.beq : litval → litval → bool
| (litval.num v₁) (litval.num v₂) := v₁ = v₂
| (litval.str v₁) (litval.str v₂) := v₁ = v₂
| _               _               := ff

instance litval.has_beq : has_beq litval := ⟨litval.beq⟩

/- Constructor information.

   - `id` is the name of the constructor in Lean.
   - `cidx` is the constructor index (aka tag).
   - `usize` is the number of arguments of type `usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `usize` (i.e., `size_t`)
scalar values, and a sequence of other scalar values. -/
structure ctor_info :=
(id : name) (cidx : nat) (usize : nat) (ssize : nat)

def ctor_info.beq : ctor_info → ctor_info → bool
| ⟨id₁, cidx₁, usize₁, ssize₁⟩ ⟨id₂, cidx₂, usize₂, ssize₂⟩ :=
  id₁ = id₂ && cidx₁ = cidx₂ && usize₁ = usize₂ && ssize₁ = ssize₂

instance ctor_info.has_beq : has_beq ctor_info := ⟨ctor_info.beq⟩

inductive expr
| ctor (i : ctor_info) (ys : list arg)
| reset (x : varid)
/- `reuse x in ctor_i ys` instruction in the paper. -/
| reuse (x : varid) (i : ctor_info) (ys : list arg)
/- Extract the `tobject` value at position `sizeof(void)*i` from `x`. -/
| proj (i : nat) (x : varid)
/- Extract the `usize` value at position `sizeof(void)*i` from `x`. -/
| uproj (i : nat) (x : varid)
/- Extract the scalar value at position `n` (in bytes) from `x`. -/
| sproj (n : nat) (x : varid)
/- Full application. -/
| fap (c : fid) (ys : list arg)
/- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
| pap (c : fid) (ys : list arg)
/- Application. `x` must be a `pap` value. -/
| ap  (x : varid) (ys : list arg)
/- Given `x : ty` where `ty` is a scalar type, this operation returns a value of type `tobject`.
   For small scalar values, the result is a tagged pointer, and no memory allocation is performed. -/
| box (ty : type) (x : varid)
/- Given `x : [t]object`, obtain the scalar value. -/
| unbox (x : varid)
| lit (v : litval)
/- Return `1 : uint8` iff `RC(x) > 1` -/
| is_shared (x : varid)
/- Return `1 : uint8` iff `x : tobject` is a tagged pointer (storing a scalar value). -/
| is_tagged_ptr (x : varid)

structure param :=
(x : name) (borrowed : bool) (ty : type)

inductive alt (fnbody : Type) : Type
| ctor (info : ctor_info) (b : fnbody) : alt
| default (b : fnbody) : alt

inductive fnbody
/- `let x : ty := e; b` -/
| vdecl (x : varid) (ty : type) (e : expr) (b : fnbody)
/- Join point declaration `let j (xs) : ty := e; b` -/
| jdecl (j : jpid) (xs : list param) (ty : type) (e : expr) (b : fnbody)
/- Store `y` at position `sizeof(void*)*i` in `x`. `x` must be a constructor object and `RC(x)` must be 1.
   This operation is not part of λ_pure is only used during optimization. -/
| set (x : varid) (i : nat) (y : varid) (b : fnbody)
/- Store `y : usize` at position `sizeof(void*)*i` in `x`. `x` must be a constructor object and `RC(x)` must be 1. -/
| uset (x : varid) (i : nat) (y : varid) (b : fnbody)
/- Store `y : ty` at position `sizeof(void*)*i + offset` in `x`. `x` must be a constructor object and `RC(x)` must be 1.
   `ty` must not be `object`, `tobject`, `irrelevant` nor `usize`. -/
| sset (x : varid) (i : nat) (offset : nat) (y : varid) (ty : type) (b : fnbody)
| release (x : varid) (i : nat) (b : fnbody)
/- RC increment for `object` -/
| inc (x : varid) (n : nat) (b : fnbody)
/- RC decrement for `object` -/
| dec (x : varid) (n : nat) (b : fnbody)
/- RC increment for `tobject` -/
| tinc (x : varid) (n : nat) (b : fnbody)
/- RC decrement for `tobject` -/
| tdec (x : varid) (n : nat) (b : fnbody)
| mdata (d : kvmap) (b : fnbody)
| case (tid : name) (cs : list (alt fnbody))
| ret (x : varid)
/- Jump to join point `j` -/
| jmp (j : jpid) (ys : list arg)
| unreachable

inductive decl
| fdecl  (f : fid) (xs : list param) (ty : type) (b : fnbody)
| extern (f : fid) (xs : list param) (ty : type)

/-- `expr.is_pure e` return `tt` iff `e` is in the `λ_pure` fragment. -/
def expr.is_pure : expr → bool
| (expr.ctor _ _)  := tt
| (expr.proj _ _)  := tt
| (expr.uproj _ _) := tt
| (expr.sproj _ _) := tt
| (expr.fap _ _)   := tt
| (expr.pap _ _)   := tt
| (expr.ap _ _)    := tt
| (expr.lit _)     := tt
| _                := ff

/-- `fnbody.is_pure b` return `tt` iff `b` is in the `λ_pure` fragment. -/
mutual def fnbody.is_pure, alts.is_pure, alt.is_pure
with fnbody.is_pure : fnbody → bool
| (fnbody.vdecl _ _ e b)    := e.is_pure && b.is_pure
| (fnbody.jdecl _ _ _ e b)  := e.is_pure && b.is_pure
| (fnbody.uset _ _ _ b)     := b.is_pure
| (fnbody.sset _ _ _ _ _ b) := b.is_pure
| (fnbody.mdata _ b)        := b.is_pure
| (fnbody.case _ cs)        := alts.is_pure cs
| (fnbody.ret _)            := tt
| (fnbody.jmp _ _)          := tt
| fnbody.unreachable        := tt
| _                         := ff
with alts.is_pure : list (alt fnbody) → bool
| []      := tt
| (a::as) := a.is_pure && alts.is_pure as
with alt.is_pure : alt fnbody → bool
| (alt.ctor _ b)  := b.is_pure
| (alt.default b) := ff

class has_alpha_eqv (α : Type) :=
(aeqv : name_map name → α → α → bool)

local notation a `=[`:50 ρ `]=`:0 b:50 := has_alpha_eqv.aeqv ρ a b

def varid.alpha_eqv (ρ : name_map name) (v₁ v₂ : varid) : bool :=
v₁ = v₂ || ρ.find v₁ = v₂

instance varid.has_aeqv : has_alpha_eqv varid := ⟨varid.alpha_eqv⟩

def arg.alpha_eqv (ρ : name_map name) : arg → arg → bool
| (arg.var v₁)   (arg.var v₂)   := v₁ =[ρ]= v₂
| arg.irrelevant arg.irrelevant := tt
| _              _              := ff

instance arg.has_aeqv : has_alpha_eqv arg := ⟨arg.alpha_eqv⟩

def args.alpha_eqv (ρ : name_map name) : list arg → list arg → bool
| []      []      := tt
| (a::as) (b::bs) := a =[ρ]= b && args.alpha_eqv as bs
| _       _       := ff

instance args.has_aeqv : has_alpha_eqv (list arg) := ⟨args.alpha_eqv⟩

def expr.alpha_eqv (ρ : name_map name) : expr → expr → bool
| (expr.ctor i₁ ys₁)      (expr.ctor i₂ ys₂)      := i₁ == i₂ && ys₁ =[ρ]= ys₂
| (expr.reset x₁)         (expr.reset x₂)         := x₁ =[ρ]= x₂
| (expr.reuse x₁ i₁ ys₁)  (expr.reuse x₂ i₂ ys₂)  := x₁ =[ρ]= x₂ && i₁ == i₂ && ys₁ =[ρ]= ys₂
| (expr.proj i₁ x₁)       (expr.proj i₂ x₂)       := i₁ = i₂ && x₁ =[ρ]= x₂
| (expr.uproj i₁ x₁)      (expr.uproj i₂ x₂)      := i₁ = i₂ && x₁ =[ρ]= x₂
| (expr.sproj n₁ x₁)      (expr.sproj n₂ x₂)      := n₁ = n₂ && x₁ =[ρ]= x₂
| (expr.fap c₁ ys₁)       (expr.fap c₂ ys₂)       := c₁ = c₂ && ys₁ =[ρ]= ys₂
| (expr.pap c₁ ys₁)       (expr.pap c₂ ys₂)       := c₁ = c₂ && ys₂ =[ρ]= ys₂
| (expr.ap x₁ ys₁)        (expr.ap x₂ ys₂)        := x₁ =[ρ]= x₂ && ys₁ =[ρ]= ys₂
| (expr.box ty₁ x₁)       (expr.box ty₂ x₂)       := ty₁ == ty₂ && x₁ =[ρ]= x₂
| (expr.unbox x₁)         (expr.unbox x₂)         := x₁ =[ρ]= x₂
| (expr.lit v₁)           (expr.lit v₂)           := v₁ == v₂
| (expr.is_shared x₁)     (expr.is_shared x₂)     := x₁ =[ρ]= x₂
| (expr.is_tagged_ptr x₁) (expr.is_tagged_ptr x₂) := x₁ =[ρ]= x₂
| _                        _                      := ff

end ir
end lean
