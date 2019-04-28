/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.name init.lean.kvmap init.lean.format
prelude

/-
Implements (extended) λPure and λRc proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λPure code, and
this part is implemented in C++. The procedures described in the paper
above are implemented in Lean.
-/
namespace Lean
namespace IR

/- Variable identifier -/
abbrev VarId := Name
/- Function identifier -/
abbrev FunId := Name
/- Join point identifier -/
abbrev JoinPointId := Name

abbrev MData := KVMap
namespace MData
abbrev empty : MData := {KVMap .}
instance : HasEmptyc MData := ⟨empty⟩
end MData

/- Low Level IR types. Most are self explanatory.

   - `usize` represents the C++ `size_t` Type. We have it here
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
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject

def IRType.beq : IRType → IRType → Bool
| IRType.float      IRType.float      := true
| IRType.uint8      IRType.uint8      := true
| IRType.uint16     IRType.uint16     := true
| IRType.uint32     IRType.uint32     := true
| IRType.uint64     IRType.uint64     := true
| IRType.usize      IRType.usize      := true
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

inductive LitVal
| num (v : Nat)
| str (v : String)

def LitVal.beq : LitVal → LitVal → Bool
| (LitVal.num v₁) (LitVal.num v₂) := v₁ == v₂
| (LitVal.str v₁) (LitVal.str v₂) := v₁ == v₂
| _               _               := false

instance LitVal.HasBeq : HasBeq LitVal := ⟨LitVal.beq⟩

/- Constructor information.

   - `name` is the Name of the Constructor in Lean.
   - `cidx` is the Constructor index (aka tag).
   - `usize` is the number of arguments of type `Usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a Constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `Usize` (i.e., `sizeT`)
scalar values, and a sequence of other scalar values. -/
structure CtorInfo :=
(name : Name) (cidx : Nat) (usize : Nat) (ssize : Nat)

def CtorInfo.beq : CtorInfo → CtorInfo → Bool
| ⟨n₁, cidx₁, usize₁, ssize₁⟩ ⟨n₂, cidx₂, usize₂, ssize₂⟩ :=
  n₁ == n₂ && cidx₁ == cidx₂ && usize₁ == usize₂ && ssize₁ == ssize₂

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
| lit (v : LitVal)
/- Return `1 : uint8` Iff `RC(x) > 1` -/
| isShared (x : VarId)
/- Return `1 : uint8` Iff `x : tobject` is a tagged pointer (storing a scalar value). -/
| isTaggedPtr (x : VarId)

structure Param :=
(x : Name) (borrowed : Bool) (ty : IRType)

inductive AltCore (FnBody : Type) : Type
| ctor (info : CtorInfo) (b : FnBody) : AltCore
| default (b : FnBody) : AltCore

inductive FnBody
/- `let x : ty := e; b` -/
| vdecl (x : VarId) (ty : IRType) (e : Expr) (b : FnBody)
/- Join point Declaration `let j (xs) : ty := e; b` -/
| jdecl (j : JoinPointId) (xs : List Param) (ty : IRType) (v : FnBody) (b : FnBody)
/- Store `y` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   This operation is not part of λPure is only used during optimization. -/
| set (x : VarId) (i : Nat) (y : VarId) (b : FnBody)
/- Store `y : Usize` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1. -/
| uset (x : VarId) (i : Nat) (y : VarId) (b : FnBody)
/- Store `y : ty` at Position `sizeof(void*)*i + offset` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
   `ty` must not be `object`, `tobject`, `irrelevant` nor `Usize`. -/
| sset (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType) (b : FnBody)
| release (x : VarId) (i : Nat) (b : FnBody)
/- RC increment for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not. -/
| inc (x : VarId) (n : Nat) (c : Bool) (b : FnBody)
/- RC decrement for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not. -/
| dec (x : VarId) (n : Nat) (c : Bool) (b : FnBody)
| mdata (d : MData) (b : FnBody)
| case (tid : Name) (x : VarId) (cs : List (AltCore FnBody))
| ret (x : VarId)
/- Jump to join point `j` -/
| jmp (j : JoinPointId) (ys : List Arg)
| unreachable

abbrev Alt := AltCore FnBody
@[pattern] abbrev Alt.ctor    := @AltCore.ctor FnBody
@[pattern] abbrev Alt.default := @AltCore.default FnBody

inductive Decl
| fdecl  (f : FunId) (xs : List Param) (ty : IRType) (b : FnBody)
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

/-- `FnBody.isPure b` return `true` Iff `b` is in the `λPure` fragment. -/
partial def FnBody.isPure : FnBody → Bool
| (FnBody.vdecl _ _ e b)    := e.isPure && b.isPure
| (FnBody.jdecl _ _ _ e b)  := e.isPure && b.isPure
| (FnBody.uset _ _ _ b)     := b.isPure
| (FnBody.sset _ _ _ _ _ b) := b.isPure
| (FnBody.mdata _ b)        := b.isPure
| (FnBody.case _ _ alts)    := alts.any $ λ alt,
  (match alt with
   | (Alt.ctor _ b)  := b.isPure
   | (Alt.default b) := false)
| (FnBody.ret _)            := true
| (FnBody.jmp _ _)          := true
| FnBody.unreachable        := true
| _                         := false

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
| (Expr.isShared x₁)      (Expr.isShared x₂)      := x₁ =[ρ]= x₂
| (Expr.isTaggedPtr x₁)   (Expr.isTaggedPtr x₂)   := x₁ =[ρ]= x₂
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

partial def FnBody.alphaEqv : VarRenaming → FnBody → FnBody → Bool
| ρ (FnBody.vdecl x₁ t₁ v₁ b₁)      (FnBody.vdecl x₂ t₂ v₂ b₂)        := t₁ == t₂ && v₁ =[ρ]= v₂ && FnBody.alphaEqv (addVarRename ρ x₁ x₂) b₁ b₂
| ρ (FnBody.jdecl j₁ ys₁ t₁ v₁ b₁)  (FnBody.jdecl j₂ ys₂ t₂ v₂ b₂)    :=
  (match addParamsRename ρ ys₁ ys₂ with
   | some ρ' := t₁ == t₂ && FnBody.alphaEqv ρ' v₁ v₂ && FnBody.alphaEqv (addVarRename ρ j₁ j₂) b₁ b₂
   | none    := false)
| ρ (FnBody.set x₁ i₁ y₁ b₁)        (FnBody.set x₂ i₂ y₂ b₂)          := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.uset x₁ i₁ y₁ b₁)       (FnBody.uset x₂ i₂ y₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.sset x₁ i₁ o₁ y₁ t₁ b₁) (FnBody.sset x₂ i₂ o₂ y₂ t₂ b₂)   :=
  x₁ =[ρ]= x₂ && i₁ = i₂ && o₁ = o₂ && y₁ =[ρ]= y₂ && t₁ == t₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.release x₁ i₁ b₁)       (FnBody.release x₂ i₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.inc x₁ n₁ c₁ b₁)        (FnBody.inc x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.dec x₁ n₁ c₁ b₁)        (FnBody.dec x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.mdata m₁ b₁)            (FnBody.mdata m₂ b₂)              := m₁ == m₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.case n₁ x₁ alts₁)       (FnBody.case n₂ x₂ alts₂)         := n₁ == n₂ && x₁ =[ρ]= x₂ && List.isEqv alts₁ alts₂ (λ alt₁ alt₂,
   match alt₁, alt₂ with
   | Alt.ctor i₁ b₁, Alt.ctor i₂ b₂ := i₁ == i₂ && FnBody.alphaEqv ρ b₁ b₂
   | Alt.default b₁, Alt.default b₂ := FnBody.alphaEqv ρ b₁ b₂
   | _,              _              := false)
| ρ (FnBody.jmp j₁ ys₁)             (FnBody.jmp j₂ ys₂)               := j₁ == j₂ && ys₁ =[ρ]= ys₂
| ρ (FnBody.ret x₁)                 (FnBody.ret x₂)                   := x₁ =[ρ]= x₂
| _ FnBody.unreachable              FnBody.unreachable                := true
| _ _                               _                                 := false

def FnBody.beq (b₁ b₂ : FnBody) : Bool :=
FnBody.alphaEqv ∅  b₁ b₂

instance FnBody.HasBeq : HasBeq FnBody := ⟨FnBody.beq⟩

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

@[inline] private def seq : Collector → Collector → Collector :=
λ k₁ k₂ bv fv, k₂ bv (k₁ bv fv)

instance : HasAndthen Collector :=
⟨seq⟩

private def collectArg : Arg → Collector
| (Arg.var x) := collectVar x
| irrelevant  := skip

private def collectArgs : List Arg → Collector
| []      := skip
| (a::as) := collectArg a; collectArgs as

private def collectExpr : Expr → Collector
| (Expr.ctor i ys)       := collectArgs ys
| (Expr.reset x)         := collectVar x
| (Expr.reuse x i ys)    := collectVar x; collectArgs ys
| (Expr.proj i x)        := collectVar x
| (Expr.uproj i x)       := collectVar x
| (Expr.sproj n x)       := collectVar x
| (Expr.fap c ys)        := collectArgs ys
| (Expr.pap c ys)        := collectArgs ys
| (Expr.ap x ys)         := collectVar x; collectArgs ys
| (Expr.box ty x)        := collectVar x
| (Expr.unbox x)         := collectVar x
| (Expr.lit v)           := skip
| (Expr.isShared x)      := collectVar x
| (Expr.isTaggedPtr x)   := collectVar x

private def collectAlts (f : FnBody → Collector) : List Alt → Collector
| []                      := skip
| (Alt.ctor _ b :: alts)  := f b; collectAlts alts
| (Alt.default b :: alts) := f b; collectAlts alts

private partial def collectFnBody : FnBody → Collector
| (FnBody.vdecl x _ v b)    := collectExpr v; withBv x (collectFnBody b)
| (FnBody.jdecl j ys _ v b) := withParams ys (collectFnBody v); withBv j (collectFnBody b)
| (FnBody.set x _ y b)      := collectVar x; collectVar y; collectFnBody b
| (FnBody.uset x _ y b)     := collectVar x; collectVar y; collectFnBody b
| (FnBody.sset x _ _ y _ b) := collectVar x; collectVar y; collectFnBody b
| (FnBody.release x _ b)    := collectVar x; collectFnBody b
| (FnBody.inc x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.dec x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.mdata _ b)        := collectFnBody b
| (FnBody.case _ x alts)    := collectVar x; collectAlts collectFnBody alts
| (FnBody.jmp j ys)         := collectVar j; collectArgs ys
| (FnBody.ret x)            := collectVar x
| FnBody.unreachable        := skip

def freeVars (b : FnBody) : VarSet :=
collectFnBody b {} {}

end freeVariables

private def formatArg : Arg → Format
| (Arg.var id)   := format id
| Arg.irrelevant := "◾"

instance argHasFormat : HasFormat Arg := ⟨formatArg⟩

private def formatArgs (as : List Arg) : Format :=
Format.joinSep as " "

instance argsHasFormat : HasFormat (List Arg) := ⟨formatArgs⟩

private def formatLitVal : LitVal → Format
| (LitVal.num v) := format v
| (LitVal.str v) := format (repr v)

instance litValHasFormat : HasFormat LitVal := ⟨formatLitVal⟩

private def formatCtorInfo : CtorInfo → Format
| { name := name, cidx := cidx, usize := usize, ssize := ssize } :=
  let r := format "ctor_" ++ format cidx in
  let r := if usize > 0 || ssize > 0 then r ++ "." ++ format usize ++ "." ++ format ssize else r in
  let r := if name != Name.anonymous then r ++ "[" ++ format name ++ "]" else r in
  r

instance ctorInfoHasFormat : HasFormat CtorInfo := ⟨formatCtorInfo⟩

private def formatExpr : Expr → Format
| (Expr.ctor i ys)       := format i ++ " " ++ format ys
| (Expr.reset x)         := "reset " ++ format x
| (Expr.reuse x i ys)    := "reuse " ++ format x ++ " in " ++ format i ++ format ys
| (Expr.proj i x)        := "proj_" ++ format i ++ " " ++ format x
| (Expr.uproj i x)       := "uproj_" ++ format i ++ " " ++ format x
| (Expr.sproj n x)       := "sproj_" ++ format n ++ " " ++ format x
| (Expr.fap c ys)        := format c ++ " " ++ format ys
| (Expr.pap c ys)        := "pap " ++ format c ++ " " ++ format ys
| (Expr.ap x ys)         := "app " ++ format x ++ " " ++ format ys
| (Expr.box _ x)         := "box " ++ format x
| (Expr.unbox x)         := "unbox " ++ format x
| (Expr.lit v)           := format v
| (Expr.isShared x)      := "isShared " ++ format x
| (Expr.isTaggedPtr x)   := "isTaggedPtr " ++ format x

instance exprHasFormat : HasFormat Expr := ⟨formatExpr⟩

private def formatIRType : IRType → Format
| IRType.float      := "float"
| IRType.uint8      := "u8"
| IRType.uint16     := "u16"
| IRType.uint32     := "u32"
| IRType.uint64     := "u64"
| IRType.usize      := "usize"
| IRType.irrelevant := "◾"
| IRType.object     := "obj"
| IRType.tobject    := "tobj"

instance typeHasFormat : HasFormat IRType := ⟨formatIRType⟩

private def formatParam : Param → Format
| { x := name, borrowed := b, ty := ty } := "(" ++ format name ++ " : " ++ (if b then "@^ " else "") ++ format ty ++ ")"

instance paramHasFormat : HasFormat Param := ⟨formatParam⟩

def formatAlt (fmt : FnBody → Format) (indent : Nat) : Alt → Format
| (Alt.ctor i b)  := format i ++ " →" ++ Format.nest indent (Format.line ++ fmt b)
| (Alt.default b) := "default →" ++ Format.nest indent (Format.line ++ fmt b)

partial def formatFnBody (indent : Nat := 2) : FnBody → Format
| (FnBody.vdecl x ty e b)    := "let " ++ format x ++ " : " ++ format ty ++ " := " ++ format e ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.jdecl j xs ty v b) := "jp " ++ format j ++ " " ++ Format.joinSep xs " " ++ " : " ++ format ty ++ " :=" ++ Format.nest indent (Format.line ++ formatFnBody v) ++ ";" ++ Format.line
| (FnBody.set x i y b)       := "set " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.uset x i y b)      := "uset " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.sset x i o y ty b) := "sset " ++ format x ++ "[" ++ format i ++ ", " ++ format o ++ "] : " ++ format ty ++ " := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.release x i b)     := "release " ++ format x ++ "[" ++ format i ++ "];" ++ Format.line ++ formatFnBody b
| (FnBody.inc x n c b)       := "inc " ++ format x ++ (if n != 1 then format n else "") ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.dec x n c b)       := "dec " ++ format x ++ (if n != 1 then format n else "") ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.mdata d b)         := "mdata " ++ format d ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.case tid x cs)     := "case " ++ format x ++ " of" ++ cs.foldl (λ r c, r ++ formatAlt formatFnBody indent c) Format.line
| (FnBody.jmp j ys)          := "jmp " ++ format j ++ " " ++ format ys
| (FnBody.ret x)             := "ret " ++ format x
| FnBody.unreachable         := "⊥"

instance fnBodyHasFormat : HasFormat FnBody := ⟨formatFnBody⟩

def formatDecl (indent : Nat := 2) : Decl → Format
| (Decl.fdecl f xs ty b) := "def " ++ format f ++ Format.joinSep xs " " ++ format " : " ++ format ty ++ " :=" ++ Format.nest indent (Format.line ++ formatFnBody indent b)
| (Decl.extern f xs ty)  := "extern " ++ format f ++ Format.joinSep xs " " ++ format " : " ++ format ty

instance declHasFormat : HasFormat Decl := ⟨formatDecl⟩

end IR
end Lean
