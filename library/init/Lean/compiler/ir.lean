/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.name init.lean.kvmap
prelude

/-
Implements (extended) λPure and λRc proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λPure code. That is,
then transformed using the procedures described in the paper above.
-/
namespace Lean
namespace IR

/- Variable identifier -/
abbrev varid := Name
/- Function identifier -/
abbrev fid := Name
/- Join point identifier -/
abbrev jpid := Name

/- Low Level IR types. Most are self explanatory.

   - `Usize` represents the C++ `sizeT` Type. We have it here
      because it is 32-bit in 32-bit machines, and 64-bit in 64-bit machines,
      and we want the C++ backend for our Compiler to generate platform independent code.

   - `irrelevant` for Lean types, propositions and proofs.

   - `object` a pointer to a value in the heap.

   - `tobject` a pointer to a value in the heap or tagged pointer
      (i.e., the least significant bit is 1) storing a scalar value.

Remark: the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.

Remark: the Lean runtime assumes that sizeof(void*) == sizeof(sizeT).
Lean cannot be compiled on old platforms where this is not True. -/
inductive IRType
| float | Uint8 | Uint16 | Uint32 | Uint64 | Usize
| irrelevant | object | tobject

def IRType.beq : IRType → IRType → Bool
| IRType.float      IRType.float      := tt
| IRType.Uint8      IRType.Uint8      := tt
| IRType.Uint16     IRType.Uint16     := tt
| IRType.Uint32     IRType.Uint32     := tt
| IRType.Uint64     IRType.Uint64     := tt
| IRType.Usize      IRType.Usize      := tt
| IRType.irrelevant IRType.irrelevant := tt
| IRType.object     IRType.object     := tt
| IRType.tobject    IRType.tobject    := tt
| _               _               := ff

instance IRType.HasBeq : HasBeq IRType := ⟨IRType.beq⟩

/- Arguments to applications, constructors, etc.
   We use `irrelevant` for Lean types, propositions and proofs that have been erased.
   Recall that for a Function `f`, we also generate `f._rarg` which does not take
   `irrelevant` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive Arg
| var (id : varid)
| irrelevant

inductive Litval
| num (v : Nat)
| str (v : String)

def Litval.beq : Litval → Litval → Bool
| (Litval.num v₁) (Litval.num v₂) := v₁ = v₂
| (Litval.str v₁) (Litval.str v₂) := v₁ = v₂
| _               _               := ff

instance Litval.HasBeq : HasBeq Litval := ⟨Litval.beq⟩

/- Constructor information.

   - `id` is the Name of the Constructor in Lean.
   - `cidx` is the Constructor index (aka tag).
   - `Usize` is the number of arguments of type `Usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a Constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `Usize` (i.e., `sizeT`)
scalar values, and a sequence of other scalar values. -/
structure CtorInfo :=
(id : Name) (cidx : Nat) (Usize : Nat) (ssize : Nat)

def CtorInfo.beq : CtorInfo → CtorInfo → Bool
| ⟨id₁, cidx₁, Usize₁, ssize₁⟩ ⟨id₂, cidx₂, Usize₂, ssize₂⟩ :=
  id₁ = id₂ && cidx₁ = cidx₂ && Usize₁ = Usize₂ && ssize₁ = ssize₂

instance CtorInfo.HasBeq : HasBeq CtorInfo := ⟨CtorInfo.beq⟩

inductive Expr
| ctor (i : CtorInfo) (ys : List Arg)
| reset (x : varid)
/- `reuse x in ctorI ys` instruction in the paper. -/
| reuse (x : varid) (i : CtorInfo) (ys : List Arg)
/- Extract the `tobject` value at Position `sizeof(void)*i` from `x`. -/
| proj (i : Nat) (x : varid)
/- Extract the `Usize` value at Position `sizeof(void)*i` from `x`. -/
| uproj (i : Nat) (x : varid)
/- Extract the scalar value at Position `n` (in bytes) from `x`. -/
| sproj (n : Nat) (x : varid)
/- Full application. -/
| fap (c : fid) (ys : List Arg)
/- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
| pap (c : fid) (ys : List Arg)
/- Application. `x` must be a `pap` value. -/
| ap  (x : varid) (ys : List Arg)
/- Given `x : ty` where `ty` is a scalar type, this operation returns a value of Type `tobject`.
   For small scalar values, the Result is a tagged pointer, and no memory allocation is performed. -/
| box (ty : IRType) (x : varid)
/- Given `x : [t]object`, obtain the scalar value. -/
| unbox (x : varid)
| lit (v : Litval)
/- Return `1 : Uint8` Iff `RC(x) > 1` -/
| isShared (x : varid)
/- Return `1 : Uint8` Iff `x : tobject` is a tagged pointer (storing a scalar value). -/
| isTaggedPtr (x : varid)

structure Param :=
(x : Name) (borrowed : Bool) (ty : IRType)

inductive AltCore (Fnbody : Type) : Type
| ctor (info : CtorInfo) (b : Fnbody) : AltCore
| default (b : Fnbody) : AltCore

inductive Fnbody
/- `let x : ty := e; b` -/
| vdecl (x : varid) (ty : IRType) (e : Expr) (b : Fnbody)
/- Join point Declaration `let j (xs) : ty := e; b` -/
| jdecl (j : jpid) (xs : List Param) (ty : IRType) (v : Fnbody) (b : Fnbody)
/- Store `y` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   This operation is not part of λPure is only used during optimization. -/
| set (x : varid) (i : Nat) (y : varid) (b : Fnbody)
/- Store `y : Usize` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1. -/
| uset (x : varid) (i : Nat) (y : varid) (b : Fnbody)
/- Store `y : ty` at Position `sizeof(void*)*i + offset` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   `ty` must not be `object`, `tobject`, `irrelevant` nor `Usize`. -/
| sset (x : varid) (i : Nat) (offset : Nat) (y : varid) (ty : IRType) (b : Fnbody)
| release (x : varid) (i : Nat) (b : Fnbody)
/- RC increment for `object`. If c = `tt`, then `inc` must check whether `x` is a tagged pointer or not. -/
| inc (x : varid) (n : Nat) (c : Bool) (b : Fnbody)
/- RC decrement for `object`. If c = `tt`, then `inc` must check whether `x` is a tagged pointer or not. -/
| dec (x : varid) (n : Nat) (c : Bool) (b : Fnbody)
| mdata (d : Kvmap) (b : Fnbody)
| case (tid : Name) (x : varid) (cs : List (AltCore Fnbody))
| ret (x : varid)
/- Jump to join point `j` -/
| jmp (j : jpid) (ys : List Arg)
| unreachable

abbrev alt := AltCore Fnbody
@[pattern] abbrev alt.ctor    := @AltCore.ctor Fnbody
@[pattern] abbrev alt.default := @AltCore.default Fnbody

inductive Decl
| fdecl  (f : fid) (xs : List Param) (ty : IRType) (b : Fnbody)
| extern (f : fid) (xs : List Param) (ty : IRType)

/-- `Expr.isPure e` return `tt` Iff `e` is in the `λPure` fragment. -/
def Expr.isPure : Expr → Bool
| (Expr.ctor _ _)  := tt
| (Expr.proj _ _)  := tt
| (Expr.uproj _ _) := tt
| (Expr.sproj _ _) := tt
| (Expr.fap _ _)   := tt
| (Expr.pap _ _)   := tt
| (Expr.ap _ _)    := tt
| (Expr.lit _)     := tt
| _                := ff

/-- `Fnbody.isPure b` return `tt` Iff `b` is in the `λPure` fragment. -/
mutual def Fnbody.isPure, alts.isPure, alt.isPure
with Fnbody.isPure : Fnbody → Bool
| (Fnbody.vdecl _ _ e b)    := e.isPure && b.isPure
| (Fnbody.jdecl _ _ _ e b)  := e.isPure && b.isPure
| (Fnbody.uset _ _ _ b)     := b.isPure
| (Fnbody.sset _ _ _ _ _ b) := b.isPure
| (Fnbody.mdata _ b)        := b.isPure
| (Fnbody.case _ _ cs)      := alts.isPure cs
| (Fnbody.ret _)            := tt
| (Fnbody.jmp _ _)          := tt
| Fnbody.unreachable        := tt
| _                         := ff
with alts.isPure : List alt → Bool
| []      := tt
| (a::as) := a.isPure && alts.isPure as
with alt.isPure : alt → Bool
| (alt.ctor _ b)  := b.isPure
| (alt.default b) := ff

abbrev varRenaming := NameMap Name

class HasAlphaEqv (α : Type) :=
(aeqv : varRenaming → α → α → Bool)

local notation a `=[`:50 ρ `]=`:0 b:50 := HasAlphaEqv.aeqv ρ a b

def varid.alphaEqv (ρ : varRenaming) (v₁ v₂ : varid) : Bool :=
match ρ.find v₁ with
| some v := v = v₂
| none   := v₁ = v₂

instance varid.hasAeqv : HasAlphaEqv varid := ⟨varid.alphaEqv⟩

def Arg.alphaEqv (ρ : varRenaming) : Arg → Arg → Bool
| (Arg.var v₁)   (Arg.var v₂)   := v₁ =[ρ]= v₂
| Arg.irrelevant Arg.irrelevant := tt
| _              _              := ff

instance Arg.hasAeqv : HasAlphaEqv Arg := ⟨Arg.alphaEqv⟩

def args.alphaEqv (ρ : varRenaming) : List Arg → List Arg → Bool
| []      []      := tt
| (a::as) (b::bs) := a =[ρ]= b && args.alphaEqv as bs
| _       _       := ff

instance args.hasAeqv : HasAlphaEqv (List Arg) := ⟨args.alphaEqv⟩

def Expr.alphaEqv (ρ : varRenaming) : Expr → Expr → Bool
| (Expr.ctor i₁ ys₁)      (Expr.ctor i₂ ys₂)      := i₁ == i₂ && ys₁ =[ρ]= ys₂
| (Expr.reset x₁)         (Expr.reset x₂)         := x₁ =[ρ]= x₂
| (Expr.reuse x₁ i₁ ys₁)  (Expr.reuse x₂ i₂ ys₂)  := x₁ =[ρ]= x₂ && i₁ == i₂ && ys₁ =[ρ]= ys₂
| (Expr.proj i₁ x₁)       (Expr.proj i₂ x₂)       := i₁ = i₂ && x₁ =[ρ]= x₂
| (Expr.uproj i₁ x₁)      (Expr.uproj i₂ x₂)      := i₁ = i₂ && x₁ =[ρ]= x₂
| (Expr.sproj n₁ x₁)      (Expr.sproj n₂ x₂)      := n₁ = n₂ && x₁ =[ρ]= x₂
| (Expr.fap c₁ ys₁)       (Expr.fap c₂ ys₂)       := c₁ = c₂ && ys₁ =[ρ]= ys₂
| (Expr.pap c₁ ys₁)       (Expr.pap c₂ ys₂)       := c₁ = c₂ && ys₂ =[ρ]= ys₂
| (Expr.ap x₁ ys₁)        (Expr.ap x₂ ys₂)        := x₁ =[ρ]= x₂ && ys₁ =[ρ]= ys₂
| (Expr.box ty₁ x₁)       (Expr.box ty₂ x₂)       := ty₁ == ty₂ && x₁ =[ρ]= x₂
| (Expr.unbox x₁)         (Expr.unbox x₂)         := x₁ =[ρ]= x₂
| (Expr.lit v₁)           (Expr.lit v₂)           := v₁ == v₂
| (Expr.isShared x₁)     (Expr.isShared x₂)     := x₁ =[ρ]= x₂
| (Expr.isTaggedPtr x₁) (Expr.isTaggedPtr x₂) := x₁ =[ρ]= x₂
| _                        _                      := ff

instance Expr.hasAeqv : HasAlphaEqv Expr:= ⟨Expr.alphaEqv⟩

def addVarRename (ρ : varRenaming) (x₁ x₂ : Name) :=
if x₁ = x₂ then ρ else ρ.insert x₁ x₂

def addParamRename (ρ : varRenaming) (p₁ p₂ : Param) : Option varRenaming :=
if p₁.ty == p₂.ty && p₁.borrowed = p₂.borrowed then some (addVarRename ρ p₁.x p₂.x)
else none

def addParamsRename : varRenaming → List Param → List Param → Option varRenaming
| ρ (p₁::ps₁) (p₂::ps₂) := do ρ ← addParamRename ρ p₁ p₂, addParamsRename ρ ps₁ ps₂
| ρ []        []        := some ρ
| _ _         _         := none

mutual def Fnbody.alphaEqv, alts.alphaEqv, alt.alphaEqv
with Fnbody.alphaEqv : varRenaming → Fnbody → Fnbody → Bool
| ρ (Fnbody.vdecl x₁ t₁ v₁ b₁)      (Fnbody.vdecl x₂ t₂ v₂ b₂)        := t₁ == t₂ && v₁ =[ρ]= v₂ && Fnbody.alphaEqv (addVarRename ρ x₁ x₂) b₁ b₂
| ρ (Fnbody.jdecl j₁ ys₁ t₁ v₁ b₁)  (Fnbody.jdecl j₂ ys₂ t₂ v₂ b₂)    :=
  (match addParamsRename ρ ys₁ ys₂ with
   | some ρ' := t₁ == t₂ && Fnbody.alphaEqv ρ' v₁ v₂ && Fnbody.alphaEqv (addVarRename ρ j₁ j₂) b₁ b₂
   | none    := ff)
| ρ (Fnbody.set x₁ i₁ y₁ b₁)        (Fnbody.set x₂ i₂ y₂ b₂)          := x₁ =[ρ]= x₂ && i₁ = i₂ && y₁ =[ρ]= y₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.uset x₁ i₁ y₁ b₁)       (Fnbody.uset x₂ i₂ y₂ b₂)         := x₁ =[ρ]= x₂ && i₁ = i₂ && y₁ =[ρ]= y₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.sset x₁ i₁ o₁ y₁ t₁ b₁) (Fnbody.sset x₂ i₂ o₂ y₂ t₂ b₂)   :=
  x₁ =[ρ]= x₂ && i₁ = i₂ && o₁ = o₂ && y₁ =[ρ]= y₂ && t₁ == t₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.release x₁ i₁ b₁)       (Fnbody.release x₂ i₂ b₂)         := x₁ =[ρ]= x₂ && i₁ = i₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.inc x₁ n₁ c₁ b₁)        (Fnbody.inc x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ = n₂ && c₁ = c₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.dec x₁ n₁ c₁ b₁)        (Fnbody.dec x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ = n₂ && c₁ = c₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.mdata m₁ b₁)            (Fnbody.mdata m₂ b₂)              := m₁ == m₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.case n₁ x₁ as₁)         (Fnbody.case n₂ x₂ as₂)           := n₁ = n₂ && x₁ =[ρ]= x₂ && alts.alphaEqv ρ as₁ as₂
| ρ (Fnbody.jmp j₁ ys₁)             (Fnbody.jmp j₂ ys₂)               := j₁ = j₂ && ys₁ =[ρ]= ys₂
| ρ (Fnbody.ret x₁)                 (Fnbody.ret x₂)                   := x₁ =[ρ]= x₂
| _ Fnbody.unreachable              Fnbody.unreachable                := tt
| _ _                               _                                 := ff
with alts.alphaEqv : varRenaming → List alt → List alt → Bool
| _ []        []        := tt
| ρ (a₁::as₁) (a₂::as₂) := alt.alphaEqv ρ a₁ a₂ && alts.alphaEqv ρ as₁ as₂
| _ _         _         := ff
with alt.alphaEqv : varRenaming → alt → alt → Bool
| ρ (alt.ctor i₁ b₁) (alt.ctor i₂ b₂) := i₁ == i₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (alt.default b₁) (alt.default b₂) := Fnbody.alphaEqv ρ b₁ b₂
| _ _                _                := ff

def Fnbody.beq (b₁ b₂ : Fnbody) : Bool :=
Fnbody.alphaEqv mkNameMap b₁ b₂

instance Fnbody.HasBeq : HasBeq Fnbody := ⟨Fnbody.beq⟩

abbrev varSet := NameSet

section freeVariables
abbrev collector := NameSet → NameSet → NameSet

@[inline] private def skip : collector :=
λ bv fv, fv

@[inline] private def var.collect (x : varid) : collector :=
λ bv fv, if bv.contains x then fv else fv.insert x

@[inline] private def withBv (x : varid) : collector → collector :=
λ k bv fv, k (bv.insert x) fv

def insertParams (s : varSet) (ys : List Param) : varSet :=
ys.foldl (λ s p, s.insert p.x) s

@[inline] private def withParams (ys : List Param) : collector → collector :=
λ k bv fv, k (insertParams bv ys) fv

@[inline] private def Seq : collector → collector → collector :=
λ k₁ k₂ bv fv, k₂ bv (k₁ bv fv)

local infix *> := Seq

private def Arg.collect : Arg → collector
| (Arg.var x) := var.collect x
| irrelevant  := skip

private def args.collect : List Arg → collector
| []      := skip
| (a::as) := Arg.collect a *> args.collect as

private def Expr.collect : Expr → collector
| (Expr.ctor i ys)       := args.collect ys
| (Expr.reset x)         := var.collect x
| (Expr.reuse x i ys)    := var.collect x *> args.collect ys
| (Expr.proj i x)        := var.collect x
| (Expr.uproj i x)       := var.collect x
| (Expr.sproj n x)       := var.collect x
| (Expr.fap c ys)        := args.collect ys
| (Expr.pap c ys)        := args.collect ys
| (Expr.ap x ys)         := var.collect x *> args.collect ys
| (Expr.box ty x)        := var.collect x
| (Expr.unbox x)         := var.collect x
| (Expr.lit v)           := skip
| (Expr.isShared x)     := var.collect x
| (Expr.isTaggedPtr x) := var.collect x

private mutual def Fnbody.collect, alts.collect, alt.collect
with Fnbody.collect : Fnbody → collector
| (Fnbody.vdecl x _ v b)    := Expr.collect v *> withBv x (Fnbody.collect b)
| (Fnbody.jdecl j ys _ v b) := withParams ys (Fnbody.collect v) *> withBv j (Fnbody.collect b)
| (Fnbody.set x _ y b)      := var.collect x *> var.collect y *> Fnbody.collect b
| (Fnbody.uset x _ y b)     := var.collect x *> var.collect y *> Fnbody.collect b
| (Fnbody.sset x _ _ y _ b) := var.collect x *> var.collect y *> Fnbody.collect b
| (Fnbody.release x _ b)    := var.collect x *> Fnbody.collect b
| (Fnbody.inc x _ _ b)      := var.collect x *> Fnbody.collect b
| (Fnbody.dec x _ _ b)      := var.collect x *> Fnbody.collect b
| (Fnbody.mdata _ b)        := Fnbody.collect b
| (Fnbody.case _ x as)      := var.collect x *> alts.collect as
| (Fnbody.jmp j ys)         := var.collect j *> args.collect ys
| (Fnbody.ret x)            := var.collect x
| Fnbody.unreachable        := skip
with alts.collect : List alt → collector
| []      := skip
| (a::as) := alt.collect a *> alts.collect as
with alt.collect : alt → collector
| (alt.ctor _ b)  := Fnbody.collect b
| (alt.default b) := Fnbody.collect b

def freeVars (b : Fnbody) : varSet :=
Fnbody.collect b mkNameSet mkNameSet

end freeVariables

end IR
end Lean
