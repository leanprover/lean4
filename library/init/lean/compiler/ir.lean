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
abbrev VarId := Name
/- Function identifier -/
abbrev FunId := Name
/- Join point identifier -/
abbrev JoinPointId := Name

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
| float | uint8 | uint16 | uint32 | uint64 | Usize
| irrelevant | object | tobject

def IRType.beq : IRType → IRType → Bool
| IRType.float      IRType.float      := true
| IRType.uint8      IRType.uint8      := true
| IRType.uint16     IRType.uint16     := true
| IRType.uint32     IRType.uint32     := true
| IRType.uint64     IRType.uint64     := true
| IRType.Usize      IRType.Usize      := true
| IRType.irrelevant IRType.irrelevant := true
| IRType.object     IRType.object     := true
| IRType.tobject    IRType.tobject    := true
| _               _                   := false

instance IRType.HasBeq : HasBeq IRType := ⟨IRType.beq⟩

/- Arguments to applications, constructors, etc.
   We use `irrelevant` for Lean types, propositions and proofs that have been erased.
   Recall that for a Function `f`, we also generate `f._rarg` which does not take
   `irrelevant` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive Arg
| var (id : VarId)
| irrelevant

inductive Litval
| num (v : Nat)
| str (v : String)

def Litval.beq : Litval → Litval → Bool
| (Litval.num v₁) (Litval.num v₂) := v₁ == v₂
| (Litval.str v₁) (Litval.str v₂) := v₁ == v₂
| _               _               := false

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
| ⟨id₁, cidx₁, usize₁, ssize₁⟩ ⟨id₂, cidx₂, usize₂, ssize₂⟩ :=
  id₁ == id₂ && cidx₁ == cidx₂ && usize₁ == usize₂ && ssize₁ == ssize₂

instance CtorInfo.HasBeq : HasBeq CtorInfo := ⟨CtorInfo.beq⟩

inductive Expr
| ctor (i : CtorInfo) (ys : List Arg)
| reset (x : VarId)
/- `reuse x in ctorI ys` instruction in the paper. -/
| reuse (x : VarId) (i : CtorInfo) (ys : List Arg)
/- Extract the `tobject` value at Position `sizeof(void)*i` from `x`. -/
| proj (i : Nat) (x : VarId)
/- Extract the `Usize` value at Position `sizeof(void)*i` from `x`. -/
| uproj (i : Nat) (x : VarId)
/- Extract the scalar value at Position `n` (in bytes) from `x`. -/
| sproj (n : Nat) (x : VarId)
/- Full application. -/
| fap (c : FunId) (ys : List Arg)
/- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
| pap (c : FunId) (ys : List Arg)
/- Application. `x` must be a `pap` value. -/
| ap  (x : VarId) (ys : List Arg)
/- Given `x : ty` where `ty` is a scalar type, this operation returns a value of Type `tobject`.
   For small scalar values, the Result is a tagged pointer, and no memory allocation is performed. -/
| box (ty : IRType) (x : VarId)
/- Given `x : [t]object`, obtain the scalar value. -/
| unbox (x : VarId)
| lit (v : Litval)
/- Return `1 : uint8` Iff `RC(x) > 1` -/
| isShared (x : VarId)
/- Return `1 : uint8` Iff `x : tobject` is a tagged pointer (storing a scalar value). -/
| isTaggedPtr (x : VarId)

structure Param :=
(x : Name) (borrowed : Bool) (ty : IRType)

inductive AltCore (Fnbody : Type) : Type
| ctor (info : CtorInfo) (b : Fnbody) : AltCore
| default (b : Fnbody) : AltCore

inductive Fnbody
/- `let x : ty := e; b` -/
| vdecl (x : VarId) (ty : IRType) (e : Expr) (b : Fnbody)
/- Join point Declaration `let j (xs) : ty := e; b` -/
| jdecl (j : JoinPointId) (xs : List Param) (ty : IRType) (v : Fnbody) (b : Fnbody)
/- Store `y` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   This operation is not part of λPure is only used during optimization. -/
| set (x : VarId) (i : Nat) (y : VarId) (b : Fnbody)
/- Store `y : Usize` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1. -/
| uset (x : VarId) (i : Nat) (y : VarId) (b : Fnbody)
/- Store `y : ty` at Position `sizeof(void*)*i + offset` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   `ty` must not be `object`, `tobject`, `irrelevant` nor `Usize`. -/
| sset (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType) (b : Fnbody)
| release (x : VarId) (i : Nat) (b : Fnbody)
/- RC increment for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not. -/
| inc (x : VarId) (n : Nat) (c : Bool) (b : Fnbody)
/- RC decrement for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not. -/
| dec (x : VarId) (n : Nat) (c : Bool) (b : Fnbody)
| mdata (d : Kvmap) (b : Fnbody)
| case (tid : Name) (x : VarId) (cs : List (AltCore Fnbody))
| ret (x : VarId)
/- Jump to join point `j` -/
| jmp (j : JoinPointId) (ys : List Arg)
| unreachable

abbrev Alt := AltCore Fnbody
@[pattern] abbrev Alt.ctor    := @AltCore.ctor Fnbody
@[pattern] abbrev Alt.default := @AltCore.default Fnbody

inductive Decl
| fdecl  (f : FunId) (xs : List Param) (ty : IRType) (b : Fnbody)
| extern (f : FunId) (xs : List Param) (ty : IRType)

/-- `Expr.isPure e` return `true` Iff `e` is in the `λPure` fragment. -/
def Expr.isPure : Expr → Bool
| (Expr.ctor _ _)  := true
| (Expr.proj _ _)  := true
| (Expr.uproj _ _) := true
| (Expr.sproj _ _) := true
| (Expr.fap _ _)   := true
| (Expr.pap _ _)   := true
| (Expr.ap _ _)    := true
| (Expr.lit _)     := true
| _                := false

/-- `Fnbody.isPure b` return `true` Iff `b` is in the `λPure` fragment. -/
mutual def Fnbody.isPure, Alts.isPure, Alt.isPure
with Fnbody.isPure : Fnbody → Bool
| (Fnbody.vdecl _ _ e b)    := e.isPure && b.isPure
| (Fnbody.jdecl _ _ _ e b)  := e.isPure && b.isPure
| (Fnbody.uset _ _ _ b)     := b.isPure
| (Fnbody.sset _ _ _ _ _ b) := b.isPure
| (Fnbody.mdata _ b)        := b.isPure
| (Fnbody.case _ _ cs)      := Alts.isPure cs
| (Fnbody.ret _)            := true
| (Fnbody.jmp _ _)          := true
| Fnbody.unreachable        := true
| _                         := false
with Alts.isPure : List Alt → Bool
| []      := true
| (a::as) := a.isPure && Alts.isPure as
with Alt.isPure : Alt → Bool
| (Alt.ctor _ b)  := b.isPure
| (Alt.default b) := false

abbrev VarRenaming := NameMap Name

class HasAlphaEqv (α : Type) :=
(aeqv : VarRenaming → α → α → Bool)

local notation a `=[`:50 ρ `]=`:0 b:50 := HasAlphaEqv.aeqv ρ a b

def VarId.alphaEqv (ρ : VarRenaming) (v₁ v₂ : VarId) : Bool :=
match ρ.find v₁ with
| some v := v == v₂
| none   := v₁ == v₂

instance VarId.hasAeqv : HasAlphaEqv VarId := ⟨VarId.alphaEqv⟩

def Arg.alphaEqv (ρ : VarRenaming) : Arg → Arg → Bool
| (Arg.var v₁)   (Arg.var v₂)   := v₁ =[ρ]= v₂
| Arg.irrelevant Arg.irrelevant := true
| _              _              := false

instance Arg.hasAeqv : HasAlphaEqv Arg := ⟨Arg.alphaEqv⟩

def args.alphaEqv (ρ : VarRenaming) : List Arg → List Arg → Bool
| []      []      := true
| (a::as) (b::bs) := a =[ρ]= b && args.alphaEqv as bs
| _       _       := false

instance args.hasAeqv : HasAlphaEqv (List Arg) := ⟨args.alphaEqv⟩

def Expr.alphaEqv (ρ : VarRenaming) : Expr → Expr → Bool
| (Expr.ctor i₁ ys₁)      (Expr.ctor i₂ ys₂)      := i₁ == i₂ && ys₁ =[ρ]= ys₂
| (Expr.reset x₁)         (Expr.reset x₂)         := x₁ =[ρ]= x₂
| (Expr.reuse x₁ i₁ ys₁)  (Expr.reuse x₂ i₂ ys₂)  := x₁ =[ρ]= x₂ && i₁ == i₂ && ys₁ =[ρ]= ys₂
| (Expr.proj i₁ x₁)       (Expr.proj i₂ x₂)       := i₁ == i₂ && x₁ =[ρ]= x₂
| (Expr.uproj i₁ x₁)      (Expr.uproj i₂ x₂)      := i₁ == i₂ && x₁ =[ρ]= x₂
| (Expr.sproj n₁ x₁)      (Expr.sproj n₂ x₂)      := n₁ == n₂ && x₁ =[ρ]= x₂
| (Expr.fap c₁ ys₁)       (Expr.fap c₂ ys₂)       := c₁ == c₂ && ys₁ =[ρ]= ys₂
| (Expr.pap c₁ ys₁)       (Expr.pap c₂ ys₂)       := c₁ == c₂ && ys₂ =[ρ]= ys₂
| (Expr.ap x₁ ys₁)        (Expr.ap x₂ ys₂)        := x₁ =[ρ]= x₂ && ys₁ =[ρ]= ys₂
| (Expr.box ty₁ x₁)       (Expr.box ty₂ x₂)       := ty₁ == ty₂ && x₁ =[ρ]= x₂
| (Expr.unbox x₁)         (Expr.unbox x₂)         := x₁ =[ρ]= x₂
| (Expr.lit v₁)           (Expr.lit v₂)           := v₁ == v₂
| (Expr.isShared x₁)     (Expr.isShared x₂)       := x₁ =[ρ]= x₂
| (Expr.isTaggedPtr x₁) (Expr.isTaggedPtr x₂)     := x₁ =[ρ]= x₂
| _                        _                      := false

instance Expr.hasAeqv : HasAlphaEqv Expr:= ⟨Expr.alphaEqv⟩

def addVarRename (ρ : VarRenaming) (x₁ x₂ : Name) :=
if x₁ = x₂ then ρ else ρ.insert x₁ x₂

def addParamRename (ρ : VarRenaming) (p₁ p₂ : Param) : Option VarRenaming :=
if p₁.ty == p₂.ty && p₁.borrowed = p₂.borrowed then some (addVarRename ρ p₁.x p₂.x)
else none

def addParamsRename : VarRenaming → List Param → List Param → Option VarRenaming
| ρ (p₁::ps₁) (p₂::ps₂) := do ρ ← addParamRename ρ p₁ p₂, addParamsRename ρ ps₁ ps₂
| ρ []        []        := some ρ
| _ _         _         := none

mutual def Fnbody.alphaEqv, Alts.alphaEqv, Alt.alphaEqv
with Fnbody.alphaEqv : VarRenaming → Fnbody → Fnbody → Bool
| ρ (Fnbody.vdecl x₁ t₁ v₁ b₁)      (Fnbody.vdecl x₂ t₂ v₂ b₂)        := t₁ == t₂ && v₁ =[ρ]= v₂ && Fnbody.alphaEqv (addVarRename ρ x₁ x₂) b₁ b₂
| ρ (Fnbody.jdecl j₁ ys₁ t₁ v₁ b₁)  (Fnbody.jdecl j₂ ys₂ t₂ v₂ b₂)    :=
  (match addParamsRename ρ ys₁ ys₂ with
   | some ρ' := t₁ == t₂ && Fnbody.alphaEqv ρ' v₁ v₂ && Fnbody.alphaEqv (addVarRename ρ j₁ j₂) b₁ b₂
   | none    := false)
| ρ (Fnbody.set x₁ i₁ y₁ b₁)        (Fnbody.set x₂ i₂ y₂ b₂)          := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.uset x₁ i₁ y₁ b₁)       (Fnbody.uset x₂ i₂ y₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.sset x₁ i₁ o₁ y₁ t₁ b₁) (Fnbody.sset x₂ i₂ o₂ y₂ t₂ b₂)   :=
  x₁ =[ρ]= x₂ && i₁ = i₂ && o₁ = o₂ && y₁ =[ρ]= y₂ && t₁ == t₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.release x₁ i₁ b₁)       (Fnbody.release x₂ i₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.inc x₁ n₁ c₁ b₁)        (Fnbody.inc x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.dec x₁ n₁ c₁ b₁)        (Fnbody.dec x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.mdata m₁ b₁)            (Fnbody.mdata m₂ b₂)              := m₁ == m₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Fnbody.case n₁ x₁ as₁)         (Fnbody.case n₂ x₂ as₂)           := n₁ == n₂ && x₁ =[ρ]= x₂ && Alts.alphaEqv ρ as₁ as₂
| ρ (Fnbody.jmp j₁ ys₁)             (Fnbody.jmp j₂ ys₂)               := j₁ == j₂ && ys₁ =[ρ]= ys₂
| ρ (Fnbody.ret x₁)                 (Fnbody.ret x₂)                   := x₁ =[ρ]= x₂
| _ Fnbody.unreachable              Fnbody.unreachable                := true
| _ _                               _                                 := false
with Alts.alphaEqv : VarRenaming → List Alt → List Alt → Bool
| _ []        []        := true
| ρ (a₁::as₁) (a₂::as₂) := Alt.alphaEqv ρ a₁ a₂ && Alts.alphaEqv ρ as₁ as₂
| _ _         _         := false
with Alt.alphaEqv : VarRenaming → Alt → Alt → Bool
| ρ (Alt.ctor i₁ b₁) (Alt.ctor i₂ b₂) := i₁ == i₂ && Fnbody.alphaEqv ρ b₁ b₂
| ρ (Alt.default b₁) (Alt.default b₂) := Fnbody.alphaEqv ρ b₁ b₂
| _ _                _                := false

def Fnbody.beq (b₁ b₂ : Fnbody) : Bool :=
Fnbody.alphaEqv ∅  b₁ b₂

instance Fnbody.HasBeq : HasBeq Fnbody := ⟨Fnbody.beq⟩

abbrev VarSet := NameSet

section freeVariables
abbrev Collector := NameSet → NameSet → NameSet

@[inline] private def skip : Collector :=
λ bv fv, fv

@[inline] private def collectVar (x : VarId) : Collector :=
λ bv fv, if bv.contains x then fv else fv.insert x

@[inline] private def withBv (x : VarId) : Collector → Collector :=
λ k bv fv, k (bv.insert x) fv

def insertParams (s : VarSet) (ys : List Param) : VarSet :=
ys.foldl (λ s p, s.insert p.x) s

@[inline] private def withParams (ys : List Param) : Collector → Collector :=
λ k bv fv, k (insertParams bv ys) fv

@[inline] private def Seq : Collector → Collector → Collector :=
λ k₁ k₂ bv fv, k₂ bv (k₁ bv fv)

local infix *> := Seq

private def collectArg : Arg → Collector
| (Arg.var x) := collectVar x
| irrelevant  := skip

private def collectArgs : List Arg → Collector
| []      := skip
| (a::as) := collectArg a *> collectArgs as

private def collectExpr : Expr → Collector
| (Expr.ctor i ys)       := collectArgs ys
| (Expr.reset x)         := collectVar x
| (Expr.reuse x i ys)    := collectVar x *> collectArgs ys
| (Expr.proj i x)        := collectVar x
| (Expr.uproj i x)       := collectVar x
| (Expr.sproj n x)       := collectVar x
| (Expr.fap c ys)        := collectArgs ys
| (Expr.pap c ys)        := collectArgs ys
| (Expr.ap x ys)         := collectVar x *> collectArgs ys
| (Expr.box ty x)        := collectVar x
| (Expr.unbox x)         := collectVar x
| (Expr.lit v)           := skip
| (Expr.isShared x)      := collectVar x
| (Expr.isTaggedPtr x)   := collectVar x

private mutual def collectFnBody, collectAlts, collectAlt
with collectFnBody : Fnbody → Collector
| (Fnbody.vdecl x _ v b)    := collectExpr v *> withBv x (collectFnBody b)
| (Fnbody.jdecl j ys _ v b) := withParams ys (collectFnBody v) *> withBv j (collectFnBody b)
| (Fnbody.set x _ y b)      := collectVar x *> collectVar y *> collectFnBody b
| (Fnbody.uset x _ y b)     := collectVar x *> collectVar y *> collectFnBody b
| (Fnbody.sset x _ _ y _ b) := collectVar x *> collectVar y *> collectFnBody b
| (Fnbody.release x _ b)    := collectVar x *> collectFnBody b
| (Fnbody.inc x _ _ b)      := collectVar x *> collectFnBody b
| (Fnbody.dec x _ _ b)      := collectVar x *> collectFnBody b
| (Fnbody.mdata _ b)        := collectFnBody b
| (Fnbody.case _ x as)      := collectVar x *> collectAlts as
| (Fnbody.jmp j ys)         := collectVar j *> collectArgs ys
| (Fnbody.ret x)            := collectVar x
| Fnbody.unreachable        := skip
with collectAlts : List Alt → Collector
| []      := skip
| (a::as) := collectAlt a *> collectAlts as
with collectAlt : Alt → Collector
| (Alt.ctor _ b)  := collectFnBody b
| (Alt.default b) := collectFnBody b

def freeVars (b : Fnbody) : VarSet :=
collectFnBody b ∅ ∅

end freeVariables

end IR
end Lean
