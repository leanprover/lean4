/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.lean.kvmap init.lean.format init.data.array
/-
Implements (extended) λPure and λRc proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λPure code, and
this part is implemented in C++. The procedures described in the paper
above are implemented in Lean.
-/
namespace Lean
namespace IR

/- Function identifier -/
abbrev FunId := Name
abbrev Index := Nat
/- Variable identifier -/
structure VarId :=
(idx : Index)
/- Join point identifier -/
structure JoinPointId :=
(idx : Index)

abbrev Index.lt (a b : Index) : Bool := a < b

namespace VarId
instance : HasBeq VarId := ⟨λ a b, a.idx == b.idx⟩
instance : HasToString VarId := ⟨λ a, "x_" ++ toString a.idx⟩
instance : HasFormat VarId := ⟨λ a, toString a⟩
end VarId

namespace JoinPointId
instance : HasBeq JoinPointId := ⟨λ a b, a.idx == b.idx⟩
instance : HasToString JoinPointId := ⟨λ a, "block_" ++ toString a.idx⟩
instance : HasFormat JoinPointId := ⟨λ a, toString a⟩
end JoinPointId

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

def IRType.isScalar : IRType → Bool
| IRType.float  := true
| IRType.uint8  := true
| IRType.uint16 := true
| IRType.uint32 := true
| IRType.uint64 := true
| IRType.usize  := true
| _             := false

instance IRType.HasBeq : HasBeq IRType := ⟨IRType.beq⟩

/- Arguments to applications, constructors, etc.
   We use `irrelevant` for Lean types, propositions and proofs that have been erased.
   Recall that for a Function `f`, we also generate `f._rarg` which does not take
   `irrelevant` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive Arg
| var (id : VarId)
| irrelevant

instance argInh : Inhabited Arg := ⟨Arg.irrelevant⟩

@[export lean.ir.mk_var_arg_core] def mkVarArg (id : VarId) : Arg := Arg.var id
@[export lean.ir.mk_irrelevant_arg_core] def mkIrrelevantArg : Arg := Arg.irrelevant

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
   - `size` is the number of arguments of type `object/tobject`.
   - `usize` is the number of arguments of type `usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a Constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `Usize` (i.e., `sizeT`)
scalar values, and a sequence of other scalar values. -/
structure CtorInfo :=
(name : Name) (cidx : Nat) (size : Nat) (usize : Nat) (ssize : Nat)

def CtorInfo.beq : CtorInfo → CtorInfo → Bool
| ⟨n₁, cidx₁, size₁, usize₁, ssize₁⟩ ⟨n₂, cidx₂, size₂, usize₂, ssize₂⟩ :=
  n₁ == n₂ && cidx₁ == cidx₂ && size₁ == size₂ && usize₁ == usize₂ && ssize₁ == ssize₂

instance CtorInfo.HasBeq : HasBeq CtorInfo := ⟨CtorInfo.beq⟩

def CtorInfo.isScalar (info : CtorInfo) : Bool :=
info.size == 0 && info.usize == 0 && info.ssize == 0

inductive Expr
| ctor (i : CtorInfo) (ys : Array Arg)
| reset (x : VarId)
/- `reuse x in ctor_i ys` instruction in the paper. -/
| reuse (x : VarId) (i : CtorInfo) (updtHeader : Bool) (ys : Array Arg)
/- Extract the `tobject` value at Position `sizeof(void*)*i` from `x`. -/
| proj (i : Nat) (x : VarId)
/- Extract the `Usize` value at Position `sizeof(void*)*i` from `x`. -/
| uproj (i : Nat) (x : VarId)
/- Extract the scalar value at Position `sizeof(void*)*n + offset` from `x`. -/
| sproj (n : Nat) (offset : Nat) (x : VarId)
/- Full application. -/
| fap (c : FunId) (ys : Array Arg)
/- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
| pap (c : FunId) (ys : Array Arg)
/- Application. `x` must be a `pap` value. -/
| ap  (x : VarId) (ys : Array Arg)
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

@[export lean.ir.mk_ctor_expr_core]  def mkCtorExpr (n : Name) (cidx : Nat) (size : Nat) (usize : Nat) (ssize : Nat) (ys : Array Arg) : Expr := Expr.ctor ⟨n, cidx, size, usize, ssize⟩ ys
@[export lean.ir.mk_proj_expr_core]  def mkProjExpr (i : Nat) (x : VarId) : Expr := Expr.proj i x
@[export lean.ir.mk_uproj_expr_core] def mkUProjExpr (i : Nat) (x : VarId) : Expr := Expr.uproj i x
@[export lean.ir.mk_sproj_expr_core] def mkSProjExpr (n : Nat) (offset : Nat) (x : VarId) : Expr := Expr.sproj n offset x
@[export lean.ir.mk_fapp_expr_core]  def mkFAppExpr (c : FunId) (ys : Array Arg) : Expr := Expr.fap c ys
@[export lean.ir.mk_papp_expr_core]  def mkPAppExpr (c : FunId) (ys : Array Arg) : Expr := Expr.pap c ys
@[export lean.ir.mk_app_expr_core]   def mkAppExpr (x : VarId) (ys : Array Arg) : Expr := Expr.ap x ys
@[export lean.ir.mk_num_expr_core]   def mkNumExpr (v : Nat) : Expr := Expr.lit (LitVal.num v)
@[export lean.ir.mk_str_expr_core]   def mkStrExpr (v : String) : Expr := Expr.lit (LitVal.str v)

structure Param :=
(x : VarId) (borrowed : Bool) (ty : IRType)

instance paramInh : Inhabited Param := ⟨{ x := { idx := 0 }, borrowed := false, ty := IRType.object }⟩

@[export lean.ir.mk_param_core] def mkParam (x : VarId) (borrowed : Bool) (ty : IRType) : Param := ⟨x, borrowed, ty⟩

inductive AltCore (FnBody : Type) : Type
| ctor (info : CtorInfo) (b : FnBody) : AltCore
| default (b : FnBody) : AltCore

inductive FnBody
/- `let x : ty := e; b` -/
| vdecl (x : VarId) (ty : IRType) (e : Expr) (b : FnBody)
/- Join point Declaration `block_j (xs) := e; b` -/
| jdecl (j : JoinPointId) (xs : Array Param) (v : FnBody) (b : FnBody)
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
| case (tid : Name) (x : VarId) (cs : Array (AltCore FnBody))
| ret (x : Arg)
/- Jump to join point `j` -/
| jmp (j : JoinPointId) (ys : Array Arg)
| unreachable

instance : Inhabited FnBody := ⟨FnBody.unreachable⟩

abbrev FnBody.nil := FnBody.unreachable

@[export lean.ir.mk_vdecl_core] def mkVDecl (x : VarId) (ty : IRType) (e : Expr) (b : FnBody) : FnBody := FnBody.vdecl x ty e b
@[export lean.ir.mk_jdecl_core] def mkJDecl (j : JoinPointId) (xs : Array Param) (v : FnBody) (b : FnBody) : FnBody := FnBody.jdecl j xs v b
@[export lean.ir.mk_uset_core] def mkUSet (x : VarId) (i : Nat) (y : VarId) (b : FnBody) : FnBody := FnBody.uset x i y b
@[export lean.ir.mk_sset_core] def mkSSet (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType) (b : FnBody) : FnBody := FnBody.sset x i offset y ty b
@[export lean.ir.mk_case_core] def mkCase (tid : Name) (x : VarId) (cs : Array (AltCore FnBody)) : FnBody := FnBody.case tid x cs
@[export lean.ir.mk_ret_core] def mkRet (x : Arg) : FnBody := FnBody.ret x
@[export lean.ir.mk_jmp_core] def mkJmp (j : JoinPointId) (ys : Array Arg) : FnBody := FnBody.jmp j ys
@[export lean.ir.mk_unreachable_core] def mkUnreachable : FnBody := FnBody.unreachable

abbrev Alt := AltCore FnBody
@[pattern] abbrev Alt.ctor    := @AltCore.ctor FnBody
@[pattern] abbrev Alt.default := @AltCore.default FnBody

instance altInh : Inhabited Alt :=
⟨Alt.default (default _)⟩

def FnBody.isTerminal : FnBody → Bool
| (FnBody.case _ _ _) := true
| (FnBody.ret _)      := true
| (FnBody.jmp _ _)    := true
| FnBody.unreachable  := true
| _                   := false

def FnBody.body : FnBody → FnBody
| (FnBody.vdecl _ _ _ b)    := b
| (FnBody.jdecl _ _ _ b)  := b
| (FnBody.set _ _ _ b)      := b
| (FnBody.uset _ _ _ b)     := b
| (FnBody.sset _ _ _ _ _ b) := b
| (FnBody.release _ _ b)    := b
| (FnBody.inc _ _ _ b)      := b
| (FnBody.dec _ _ _ b)      := b
| (FnBody.mdata _ b)        := b
| other                     := other

def FnBody.setBody : FnBody → FnBody → FnBody
| (FnBody.vdecl x t v _)    b := FnBody.vdecl x t v b
| (FnBody.jdecl j xs v _)   b := FnBody.jdecl j xs v b
| (FnBody.set x i y _)      b := FnBody.set x i y b
| (FnBody.uset x i y _)     b := FnBody.uset x i y b
| (FnBody.sset x i o y t _) b := FnBody.sset x i o y t b
| (FnBody.release x i _)    b := FnBody.release x i b
| (FnBody.inc x n c _)      b := FnBody.inc x n c b
| (FnBody.dec x n c _)      b := FnBody.dec x n c b
| (FnBody.mdata d _)        b := FnBody.mdata d b
| other                     b := other

infix `<;>`:65 := FnBody.setBody

@[inline] def FnBody.resetBody (b : FnBody) : FnBody :=
b <;> FnBody.nil

/- If b is a non terminal, then return a pair `(c, b')` s.t. `b == c <;> b'`,
   and c.body == FnBody.nil -/
@[inline] def FnBody.split (b : FnBody) : FnBody × FnBody :=
let b' := b.body in
let c  := b.resetBody in
(c, b')

def AltCore.body : Alt → FnBody
| (Alt.ctor _ b)  := b
| (Alt.default b) := b

def AltCore.setBody : Alt → FnBody → Alt
| (Alt.ctor c _) b  := Alt.ctor c b
| (Alt.default _) b := Alt.default b

@[inline] def AltCore.modifyBody (f : FnBody → FnBody) : AltCore FnBody → Alt
| (Alt.ctor c b)  := Alt.ctor c (f b)
| (Alt.default b) := Alt.default (f b)

@[inline] def AltCore.mmodifyBody {m : Type → Type} [Monad m] (f : FnBody → m FnBody) : AltCore FnBody → m Alt
| (Alt.ctor c b)  := Alt.ctor c <$> f b
| (Alt.default b) := Alt.default <$> f b

def Alt.isDefault : Alt → Bool
| (Alt.ctor _ _)  := false
| (Alt.default _) := true

def push (bs : Array FnBody) (b : FnBody) : Array FnBody :=
let b := b.resetBody in
bs.push b

partial def flattenAux : FnBody → Array FnBody → (Array FnBody) × FnBody
| b r :=
  if b.isTerminal then (r, b)
  else flattenAux b.body (push r b)

def FnBody.flatten (b : FnBody) : (Array FnBody) × FnBody :=
flattenAux b Array.empty

partial def reshapeAux : Array FnBody → Nat → FnBody → FnBody
| a i b :=
  if i == 0 then b
  else
    let i         := i - 1 in
    let (curr, a) := a.swapAt i (default _) in
    let b         := curr <;> b in
    reshapeAux a i b

def reshape (bs : Array FnBody) (term : FnBody) : FnBody :=
reshapeAux bs bs.size term

@[inline] def modifyJPs (bs : Array FnBody) (f : FnBody → FnBody) : Array FnBody :=
bs.hmap $ λ b, match b with
  | FnBody.jdecl j xs v k := FnBody.jdecl j xs (f v) k
  | other                 := other

@[inline] def mmodifyJPs {m : Type → Type} [Monad m] (bs : Array FnBody) (f : FnBody → m FnBody) : m (Array FnBody) :=
bs.hmmap $ λ b, match b with
  | FnBody.jdecl j xs v k := do v ← f v, pure $ FnBody.jdecl j xs v k
  | other                 := pure other

@[export lean.ir.mk_alt_core] def mkAlt (n : Name) (cidx : Nat) (size : Nat) (usize : Nat) (ssize : Nat) (b : FnBody) : Alt := Alt.ctor ⟨n, cidx, size, usize, ssize⟩ b

inductive Decl
| fdecl  (f : FunId) (xs : Array Param) (ty : IRType) (b : FnBody)
| extern (f : FunId) (xs : Array Param) (ty : IRType)

def Decl.id : Decl → FunId
| (Decl.fdecl f _ _ _) := f
| (Decl.extern f _ _)  := f

def Decl.params : Decl → Array Param
| (Decl.fdecl _ xs _ _) := xs
| (Decl.extern _ xs _)  := xs

def Decl.resultType : Decl → IRType
| (Decl.fdecl _ _ t _) := t
| (Decl.extern _ _ t)  := t

@[export lean.ir.mk_decl_core] def mkDecl (f : FunId) (xs : Array Param) (ty : IRType) (b : FnBody) : Decl := Decl.fdecl f xs ty b

/-- `Expr.isPure e` return `true` Iff `e` is in the `λPure` fragment. -/
def Expr.isPure : Expr → Bool
| (Expr.ctor _ _)    := true
| (Expr.proj _ _)    := true
| (Expr.uproj _ _)   := true
| (Expr.sproj _ _ _) := true
| (Expr.fap _ _)     := true
| (Expr.pap _ _)     := true
| (Expr.ap _ _)      := true
| (Expr.lit _)       := true
| _                  := false

/-- `FnBody.isPure b` return `true` Iff `b` is in the `λPure` fragment. -/
partial def FnBody.isPure : FnBody → Bool
| (FnBody.vdecl _ _ e b)    := e.isPure && b.isPure
| (FnBody.jdecl _ _ e b)    := e.isPure && b.isPure
| (FnBody.uset _ _ _ b)     := b.isPure
| (FnBody.sset _ _ _ _ _ b) := b.isPure
| (FnBody.mdata _ b)        := b.isPure
| (FnBody.case _ _ alts)    := alts.any $ λ alt,
  match alt with
  | (Alt.ctor _ b)  := b.isPure
  | (Alt.default b) := false
| (FnBody.ret _)            := true
| (FnBody.jmp _ _)          := true
| FnBody.unreachable        := true
| _                         := false

/-- Set of variable and join point names -/
abbrev IndexSet := RBTree Index Index.lt
instance vsetInh : Inhabited IndexSet := ⟨{}⟩

inductive ContextEntry
| param     : IRType → ContextEntry
| localVar  : IRType → Expr → ContextEntry
| joinPoint : Array Param → FnBody → ContextEntry

abbrev Context := RBMap Index ContextEntry Index.lt

def Context.addLocal (ctx : Context) (x : VarId) (t : IRType) (v : Expr) : Context :=
ctx.insert x.idx (ContextEntry.localVar t v)

def Context.addJP (ctx : Context) (j : JoinPointId) (xs : Array Param) (b : FnBody) : Context :=
ctx.insert j.idx (ContextEntry.joinPoint xs b)

def Context.addParam (ctx : Context) (p : Param) : Context :=
ctx.insert p.x.idx (ContextEntry.param p.ty)

def Context.addParams (ctx : Context) (ps : Array Param) : Context :=
ps.foldl Context.addParam ctx

def Context.isJP (ctx : Context) (idx : Index) : Bool :=
match ctx.find idx with
| some (ContextEntry.joinPoint _ _) := true
| other := false

def Context.getJPBody (ctx : Context) (j : JoinPointId) : Option FnBody :=
match ctx.find j.idx with
| some (ContextEntry.joinPoint _ b) := some b
| other := none

def Context.getJPParams (ctx : Context) (j : JoinPointId) : Option (Array Param) :=
match ctx.find j.idx with
| some (ContextEntry.joinPoint ys _) := some ys
| other := none

def Context.isParam (ctx : Context) (idx : Index) : Bool :=
match ctx.find idx with
| some (ContextEntry.param _) := true
| other := false

def Context.isLocalVar (ctx : Context) (idx : Index) : Bool :=
match ctx.find idx with
| some (ContextEntry.localVar _ _) := true
| other := false

def Context.contains (ctx : Context) (idx : Index) : Bool :=
ctx.contains idx

def Context.eraseJoinPointDecl (ctx : Context) (j : JoinPointId) : Context :=
ctx.erase j.idx

def Context.getType (ctx : Context) (x : VarId) : Option IRType :=
match ctx.find x.idx with
| some (ContextEntry.param t) := some t
| some (ContextEntry.localVar t _) := some t
| other := none

abbrev IndexRenaming := RBMap Index Index Index.lt

class HasAlphaEqv (α : Type) :=
(aeqv : IndexRenaming → α → α → Bool)

local notation a `=[`:50 ρ `]=`:0 b:50 := HasAlphaEqv.aeqv ρ a b

def VarId.alphaEqv (ρ : IndexRenaming) (v₁ v₂ : VarId) : Bool :=
match ρ.find v₁.idx with
| some v := v == v₂.idx
| none   := v₁ == v₂

instance VarId.hasAeqv : HasAlphaEqv VarId := ⟨VarId.alphaEqv⟩

def Arg.alphaEqv (ρ : IndexRenaming) : Arg → Arg → Bool
| (Arg.var v₁)   (Arg.var v₂)   := v₁ =[ρ]= v₂
| Arg.irrelevant Arg.irrelevant := true
| _              _              := false

instance Arg.hasAeqv : HasAlphaEqv Arg := ⟨Arg.alphaEqv⟩

def args.alphaEqv (ρ : IndexRenaming) (args₁ args₂ : Array Arg) : Bool :=
Array.isEqv args₁ args₂ (λ a b, a =[ρ]= b)

instance args.hasAeqv : HasAlphaEqv (Array Arg) := ⟨args.alphaEqv⟩

def Expr.alphaEqv (ρ : IndexRenaming) : Expr → Expr → Bool
| (Expr.ctor i₁ ys₁)        (Expr.ctor i₂ ys₂)        := i₁ == i₂ && ys₁ =[ρ]= ys₂
| (Expr.reset x₁)           (Expr.reset x₂)           := x₁ =[ρ]= x₂
| (Expr.reuse x₁ i₁ u₁ ys₁) (Expr.reuse x₂ i₂ u₂ ys₂) := x₁ =[ρ]= x₂ && i₁ == i₂ && u₁ == u₂ && ys₁ =[ρ]= ys₂
| (Expr.proj i₁ x₁)         (Expr.proj i₂ x₂)         := i₁ == i₂ && x₁ =[ρ]= x₂
| (Expr.uproj i₁ x₁)        (Expr.uproj i₂ x₂)        := i₁ == i₂ && x₁ =[ρ]= x₂
| (Expr.sproj n₁ o₁ x₁)     (Expr.sproj n₂ o₂ x₂)     := n₁ == n₂ && o₁ == o₂ && x₁ =[ρ]= x₂
| (Expr.fap c₁ ys₁)         (Expr.fap c₂ ys₂)         := c₁ == c₂ && ys₁ =[ρ]= ys₂
| (Expr.pap c₁ ys₁)         (Expr.pap c₂ ys₂)         := c₁ == c₂ && ys₂ =[ρ]= ys₂
| (Expr.ap x₁ ys₁)          (Expr.ap x₂ ys₂)          := x₁ =[ρ]= x₂ && ys₁ =[ρ]= ys₂
| (Expr.box ty₁ x₁)         (Expr.box ty₂ x₂)         := ty₁ == ty₂ && x₁ =[ρ]= x₂
| (Expr.unbox x₁)           (Expr.unbox x₂)           := x₁ =[ρ]= x₂
| (Expr.lit v₁)             (Expr.lit v₂)             := v₁ == v₂
| (Expr.isShared x₁)        (Expr.isShared x₂)        := x₁ =[ρ]= x₂
| (Expr.isTaggedPtr x₁)     (Expr.isTaggedPtr x₂)     := x₁ =[ρ]= x₂
| _                          _                        := false

instance Expr.hasAeqv : HasAlphaEqv Expr:= ⟨Expr.alphaEqv⟩

def addVarRename (ρ : IndexRenaming) (x₁ x₂ : Nat) :=
if x₁ == x₂ then ρ else ρ.insert x₁ x₂

def addParamRename (ρ : IndexRenaming) (p₁ p₂ : Param) : Option IndexRenaming :=
if p₁.ty == p₂.ty && p₁.borrowed = p₂.borrowed then some (addVarRename ρ p₁.x.idx p₂.x.idx)
else none

def addParamsRename (ρ : IndexRenaming) (ps₁ ps₂ : Array Param) : Option IndexRenaming :=
if ps₁.size != ps₂.size then none
else Array.foldl₂ (λ ρ p₁ p₂, do ρ ← ρ, addParamRename ρ p₁ p₂) (some ρ) ps₁ ps₂

partial def FnBody.alphaEqv : IndexRenaming → FnBody → FnBody → Bool
| ρ (FnBody.vdecl x₁ t₁ v₁ b₁)      (FnBody.vdecl x₂ t₂ v₂ b₂)        := t₁ == t₂ && v₁ =[ρ]= v₂ && FnBody.alphaEqv (addVarRename ρ x₁.idx x₂.idx) b₁ b₂
| ρ (FnBody.jdecl j₁ ys₁ v₁ b₁)  (FnBody.jdecl j₂ ys₂ v₂ b₂)          := match addParamsRename ρ ys₁ ys₂ with
  | some ρ' := FnBody.alphaEqv ρ' v₁ v₂ && FnBody.alphaEqv (addVarRename ρ j₁.idx j₂.idx) b₁ b₂
  | none    := false
| ρ (FnBody.set x₁ i₁ y₁ b₁)        (FnBody.set x₂ i₂ y₂ b₂)          := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.uset x₁ i₁ y₁ b₁)       (FnBody.uset x₂ i₂ y₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && y₁ =[ρ]= y₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.sset x₁ i₁ o₁ y₁ t₁ b₁) (FnBody.sset x₂ i₂ o₂ y₂ t₂ b₂)   :=
  x₁ =[ρ]= x₂ && i₁ = i₂ && o₁ = o₂ && y₁ =[ρ]= y₂ && t₁ == t₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.release x₁ i₁ b₁)       (FnBody.release x₂ i₂ b₂)         := x₁ =[ρ]= x₂ && i₁ == i₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.inc x₁ n₁ c₁ b₁)        (FnBody.inc x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.dec x₁ n₁ c₁ b₁)        (FnBody.dec x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ == n₂ && c₁ == c₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.mdata m₁ b₁)            (FnBody.mdata m₂ b₂)              := m₁ == m₂ && FnBody.alphaEqv ρ b₁ b₂
| ρ (FnBody.case n₁ x₁ alts₁)       (FnBody.case n₂ x₂ alts₂)         := n₁ == n₂ && x₁ =[ρ]= x₂ && Array.isEqv alts₁ alts₂ (λ alt₁ alt₂,
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

end IR
end Lean
