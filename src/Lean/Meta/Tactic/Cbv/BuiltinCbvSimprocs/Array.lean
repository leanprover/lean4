/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski, Robin Arnez
-/
module

prelude
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InferType
import Init.CbvSimproc
import Init.Sym.TreeArray
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.Tactic.Cbv.Util
import Init.GetElem
import Init.Data.Array.OfFn
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.AppBuilder

namespace Lean.Meta.Tactic.Cbv

open Sym.Simp Sym.Internal
open Lean.Sym

/-- Extract elements from an array literal (`Array.mk` applied to a list literal). -/
def getArrayLitElems? (e : Expr) : Option <| Array Expr :=
  match_expr e with
  | Array.mk _ as => getListLitElems as
  | _ => none

structure ArrayBuilderCtx where
  mk' ::
  u : Level
  α : Expr
  fullSingleFn : Expr -- Shared version of `@FullBlock.single α`
  fullSplitFn : Expr -- Shared version of `@FullBlock.split α`
  partialEmpty : Expr -- Shared version of `@PartialBlock.empty α`
  partialSplitFn : Expr -- Shared version of `@PartialBlock.split α`
  partialToArrayFn : Expr -- Shared version of `@PartialBlock.toArray α`
  rflTrue : Expr -- Shared version of `rfl : true = true`

def ArrayBuilderCtx.mk (u : Level) (α : Expr) : Sym.SymM ArrayBuilderCtx := do
  return {
    u, α
    fullSingleFn := ← mkAppS (← mkConstS ``FullBlock.single [u]) α
    fullSplitFn := ← mkAppS (← mkConstS ``FullBlock.split [u]) α
    partialEmpty := ← mkAppS (← mkConstS ``PartialBlock.empty [u]) α
    partialSplitFn := ← mkAppS (← mkConstS ``PartialBlock.split [u]) α
    partialToArrayFn := ← mkAppS (← mkConstS ``PartialBlock.toArray [u]) α
    rflTrue := ← Sym.share <| reflBoolTrue
  }

namespace ArrayBuilderCtx

def fullSingle (ctx : ArrayBuilderCtx) (x : Expr) : Sym.SymM Expr := do
  mkAppS ctx.fullSingleFn x

def fullSplit (ctx : ArrayBuilderCtx) (n : Expr) (l r : Expr) : Sym.SymM Expr := do
  mkAppS₃ ctx.fullSplitFn n l r

def partialSplit (ctx : ArrayBuilderCtx) (n m : Expr) (l r : Expr) : Sym.SymM Expr := do
  mkAppS₅ ctx.partialSplitFn n m l r ctx.rflTrue

def toArray (ctx : ArrayBuilderCtx) (n : Expr) (x : Expr) : Sym.SymM Expr := do
  mkAppS₂ ctx.partialToArrayFn n x

/-- Creates a `FullBlock α n` consisting of the values in `elems[start...(start + 2^n)]` -/
def mkFullOfArray (ctx : ArrayBuilderCtx) (lits : Array Expr)
    (elems : Array Expr) (start : Nat) (n : Nat) : Sym.SymM Expr := do
  match n with
  | 0 => ctx.fullSingle elems[start]!
  | k + 1 =>
    ctx.fullSplit lits[k]!
      (← ctx.mkFullOfArray lits elems start k)
      (← ctx.mkFullOfArray lits elems (start + 1 <<< k) k)

/--
Returns `(n, block)` where `block : FullBlock α n` consists of the values in `elems[start...stop]`
-/
def mkPartialOfArray (ctx : ArrayBuilderCtx) (lits : Array Expr)
    (elems : Array Expr) (start stop : Nat) : Sym.SymM (Nat × Expr) := do
  if stop ≤ start then
    return (0, ctx.partialEmpty)
  let leftN := (stop - start).log2
  let mid := start + 1 <<< leftN
  let left ← ctx.mkFullOfArray lits elems start leftN
  let (rightN, right) ← ctx.mkPartialOfArray lits elems mid stop
  assert! rightN ≤ leftN
  return (leftN + 1, ← ctx.partialSplit lits[leftN]! lits[rightN]! left right)
termination_by stop - start
decreasing_by simp_all [Nat.shiftLeft_eq]; have := Nat.two_pow_pos (stop - start).log2; omega

def arrayToPartialBlock (ctx : ArrayBuilderCtx) (elems : Array Expr) : Sym.SymM (Expr × Expr) := do
  let size := elems.size
  let numNeededLits := size.log2 + 2
  let lits ← Array.ofFnM fun i : Fin numNeededLits => mkLitS (.natVal i)
  let (n, block) ← ctx.mkPartialOfArray lits elems 0 size
  return (lits[n]!, block)

/--
Returns `(n, block)` where `block : FullBlock α n` consists of the values in `elems[start...stop]`
-/
def replicatePartial (ctx : ArrayBuilderCtx) (lits : Array Expr) (fulls : Array Expr)
    (val : Expr) (size : Nat) : Sym.SymM (Nat × Expr) := do
  if size = 0 then
    return (0, ctx.partialEmpty)
  let leftN := size.log2
  let left := fulls[leftN]!
  let (rightN, right) ← ctx.replicatePartial lits fulls val (size - 1 <<< leftN)
  assert! rightN ≤ leftN
  return (leftN + 1, ← ctx.partialSplit lits[leftN]! lits[rightN]! left right)
termination_by size
decreasing_by simp_all [Nat.shiftLeft_eq]; have := Nat.two_pow_pos size.log2; omega

def replicateToPartialBlock (ctx : ArrayBuilderCtx) (val : Expr) (size : Nat) :
    Sym.SymM (Expr × Expr) := do
  let numNeededLits := size.log2 + 2
  let numNeededFulls := size.log2 + 1
  let lits ← Array.ofFnM fun i : Fin numNeededLits => mkLitS (.natVal i)
  let mut fulls := #[← ctx.fullSingle val]
  for i in 1...numNeededFulls do
    fulls := fulls.push <| ← ctx.fullSplit lits[i - 1]! fulls.back! fulls.back!
  let (n, block) ← ctx.replicatePartial lits fulls val size
  return (lits[n]!, block)

end ArrayBuilderCtx

builtin_cbv_simproc ↓ simpPartialToArray (PartialBlock.toArray _) := fun e => do
  let_expr PartialBlock.toArray _ _ _ := e | return .rfl
  -- Don't visit `PartialBlock.toArray`
  -- Note: we use as an invariant that the elements inside of a `PartialBlock` are
  -- always simplified
  return .rfl (done := true)

builtin_cbv_simproc cbv_eval simpArrayMk (Array.mk _) := fun e => do
  let_expr c@Array.mk α list := e | return .rfl
  let some elems := getListLitElems list | return .rfl
  let u : Level := c.constLevels![0]!
  let ctx ← ArrayBuilderCtx.mk u α
  let (n, block) ← ctx.arrayToPartialBlock elems
  let proof := mkApp5 (.const ``PartialBlock.arrayMk_eq [u]) α n list block (← Sym.mkEqRefl list)
  return .step (← ctx.toArray n block) proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayReplicate (Array.replicate _ _) := fun e => do
  let_expr c@Array.replicate α sizeExpr val := e | return .rfl
  let some size := Sym.getNatValue? sizeExpr | return .rfl
  let u : Level := c.constLevels![0]!
  let ctx ← ArrayBuilderCtx.mk u α
  let (n, block) ← ctx.replicateToPartialBlock val size
  let reflZero := mkApp2 (.const ``rfl [1]) (.const ``Nat []) (.lit (.natVal 0))
  let proof := mkApp5 (.const ``PartialBlock.replicate_eq [u]) α val n sizeExpr reflZero
  return .step (← ctx.toArray n block) proof (done := true)

partial def extractFullBlockElems (x : Expr) (acc : Array Expr) :
    OptionT Sym.SymM (Array Expr) := do
  match_expr x with
  | FullBlock.single _ val => return acc.push val
  | FullBlock.split _ _ l r => extractFullBlockElems r (← extractFullBlockElems l acc)
  | _ => failure

partial def extractPartialBlockElems (x : Expr) (acc : Array Expr) :
    OptionT Sym.SymM (Array Expr) := do
  match_expr x with
  | PartialBlock.empty _ => return acc
  | PartialBlock.split _ _ _ l r _ => extractPartialBlockElems r (← extractFullBlockElems l acc)
  | _ =>
    trace[debug] "Failed `extractPartialBlockElems` at {x}"
    failure

builtin_cbv_simproc cbv_eval simpArrayToList (Array.toList _) := fun e => do
  let_expr Array.toList _ xs := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some elems ← (extractPartialBlockElems block #[]).run | return .rfl
  let u : Level := c.constLevels![0]!
  let nil ← mkAppS (← mkConstS ``List.nil [u]) α
  let cons ← mkAppS (← mkConstS ``List.cons [u]) α
  let mut list := nil
  let mut i := elems.size
  while i ≠ 0 do
    i := i - 1
    list ← mkAppS₂ cons elems[i]! list
  let proof := mkApp3 (.const ``PartialBlock.toList_toArray [u]) α n block
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``List [u]) α) e list
  let proof := mkExpectedPropHint proof eq
  return .step list proof (done := true)

partial def partialBlockSize (x : Expr) (acc : Nat) : OptionT Sym.SymM Nat := do
  match_expr x with
  | PartialBlock.empty _ => return acc
  | PartialBlock.split _ n _ _ r _ =>
    let some val := n.rawNatLit? |
      trace[debug] "Failed `partialBlockSize` at {x}"
      failure
    partialBlockSize r (acc + 1 <<< val)
  | _ =>
    trace[debug] "Failed `partialBlockSize` at {x}"
    failure

builtin_cbv_simproc cbv_eval simpArraySize (Array.size _) := fun e => do
  let_expr Array.size _ xs := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some size ← (partialBlockSize block 0).run | return .rfl
  let u : Level := c.constLevels![0]!
  let rhs ← Sym.share <| toExpr size
  let actualRhs := mkApp3 (.const ``PartialBlock.size [u]) α n block
  let proof := mkApp3 (.const ``PartialBlock.size_toArray [u]) α n block
  let actualEq := mkApp3 (.const ``Eq [1]) (.const ``Nat []) e actualRhs
  -- we need eager reduction here because we use `Nat.add` on terms that may contain free variables
  let proof := mkApp2 (.const ``eagerReduce [0]) actualEq proof
  let eq := mkApp3 (.const ``Eq [1]) (.const ``Nat []) e rhs
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

inductive ExprPushResult where
  | part (e : Expr)
  | full (e : Expr)

@[inline]
def ExprPushResult.toExpr (u : Level) (α : Expr) (n : Expr) (res : ExprPushResult) : Expr :=
  match res with
  | .part e => mkApp3 (.const ``PushResult.part [u]) α n e
  | .full e => mkApp3 (.const ``PushResult.full [u]) α n e

@[inline]
def ExprPushResult.toProof (u : Level) (α : Expr) (n : Expr) (origBlock : Expr) (value : Expr)
    (res : ExprPushResult) : Expr :=
  let refl := mkApp2 (.const ``Eq.refl [u.succ]) (mkApp2 (.const ``PushResult [u]) α n)
    (res.toExpr u α n)
  match res with
  | .part e => mkApp6 (.const ``PartialBlock.push_part [u]) α n origBlock e value refl
  | .full e => mkApp6 (.const ``PartialBlock.push_full [u]) α n origBlock e value refl

/--
Given `x : PartialBlock α n` and `v : α`, returns `x.push v` as an `ExprPushResult`. Mimics the
logic of `PartialBlock.push`.
-/
partial def partialBlockPush (x : Expr) (v : Expr) : OptionT Sym.SymM ExprPushResult := do
  match_expr x with
  | c@PartialBlock.empty α =>
    let u := c.constLevels![0]!
    return .full (← mkAppS₂ (← mkConstS ``FullBlock.single [u]) α v)
  | c@PartialBlock.split α n m l r h =>
    match ← partialBlockPush r v with
    | .part block =>
      -- partial block: just update the right-hand side
      return .part <| ← mkAppS₂ x.appFn!.appFn! block h
    | .full block =>
      -- full block: either partial or full depending on the sizes
      let some leftSize := n.rawNatLit? | failure
      let some rightSize := m.rawNatLit? | failure
      assert! rightSize ≤ leftSize
      assert! h == reflBoolTrue
      let u := c.constLevels![0]!
      if leftSize = rightSize then
        -- both are now equal sized full blocks: create a full block
        return .full (← mkAppS₄ (← mkConstS ``FullBlock.split [u]) α n l block)
      else
        -- the right side is smaller: fit it into a new partial block
        let split := x.getBoundedAppFn 5 -- @PartialBlock.split.{u} α
        let empty ← mkAppS (← mkConstS ``PartialBlock.empty [u]) α
        let rightBlock ← mkAppS₅ split m (← mkLitS (.natVal 0)) block empty h
        return .part <| ← mkAppS₅ split n (← mkLitS (.natVal (rightSize + 1))) l rightBlock h
  | _ => failure

builtin_cbv_simproc cbv_eval simpArrayPush (Array.push _ _) := fun e => do
  let_expr Array.push _ xs val := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let u : Level := c.constLevels![0]!
  let some pushResult ← (partialBlockPush block val).run | return .rfl
  let proof := pushResult.toProof u α n block val
  let (n', newBlock) ← match pushResult with
    | .part newBlock =>
      -- already a partial block, nothing to do
      pure (n, newBlock)
    | .full newFullBlock =>
      -- convert full block into partial block
      let some size := n.rawNatLit? | failure
      let empty ← mkAppS (← mkConstS ``PartialBlock.empty [u]) α
      let newBlock ← mkAppS₆ (← mkConstS ``PartialBlock.split [u]) α n
        (← mkLitS (.natVal 0)) newFullBlock empty (← Sym.share reflBoolTrue)
      pure (← mkLitS (.natVal (size + 1)), newBlock)
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [u]) α n' newBlock
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Array [u]) α) e rhs
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

inductive ExprPopResult where
  | empty
  | done (e : Expr)
  | shrink (e : Expr) (newN : Expr)

@[inline]
def ExprPopResult.toExpr (u : Level) (α : Expr) (n : Expr) (res : ExprPopResult) : Expr :=
  match res with
  | .empty => mkApp (.const ``PopResult.empty [u]) α
  | .done e => mkApp3 (.const ``PopResult.done [u]) α n e
  | .shrink e newN => mkApp3 (.const ``PopResult.shrink [u]) α newN e

@[inline]
def ExprPopResult.toProof (u : Level) (α : Expr) (n : Expr) (origBlock : Expr)
    (res : ExprPopResult) : Expr :=
  let refl := mkApp2 (.const ``Eq.refl [u.succ]) (mkApp2 (.const ``PopResult [u]) α n)
    (res.toExpr u α n)
  match res with
  | .empty => .app (.const ``PartialBlock.pop_toArray_empty [u]) α
  | .done e => mkApp5 (.const ``PartialBlock.pop_done [u]) α n origBlock e refl
  | .shrink e newN => mkApp5 (.const ``PartialBlock.pop_shrink [u]) α newN origBlock e refl

/-- Given `x : FullBlock α n`, returns `x.pop`. -/
partial def fullBlockPop (x : Expr) : OptionT Sym.SymM Expr := do
  match_expr x with
  | c@FullBlock.single α _val => mkAppS (← mkConstS ``PartialBlock.empty c.constLevels!) α
  | c@FullBlock.split α n l r =>
    let r ← fullBlockPop r
    mkAppS₆ (← mkConstS ``PartialBlock.split c.constLevels!) α n n l r (← Sym.share reflBoolTrue)
  | _ => failure

/--
Given `x : PartialBlock α n`, returns `x.pop` as an `ExprPopResult`. Mimics the logic of
`PartialBlock.pop`.
-/
partial def partialBlockPop (x : Expr) : OptionT Sym.SymM ExprPopResult := do
  match_expr x with
  | PartialBlock.empty _ => return .empty
  | PartialBlock.split _ n _ l r h =>
    match ← partialBlockPop r with
    | .empty => return .shrink (← fullBlockPop l) n
    | .done block =>
      -- partial block of same size: just update the right-hand side
      return .done <| ← mkAppS₂ x.appFn!.appFn! block h
    | .shrink block newM =>
      -- partial block of smaller size: just update the right-hand side
      let split := x.getBoundedAppFn 4 -- @PartialBlock.split.{u} α n
      assert! h == reflBoolTrue
      return .done <| ← mkAppS₄ split newM l block h
  | _ => failure

builtin_cbv_simproc cbv_eval simpArrayPop (Array.pop _) := fun e => do
  let_expr Array.pop _ xs := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let u : Level := c.constLevels![0]!
  let some popResult ← (partialBlockPop block).run | return .rfl
  let proof := popResult.toProof u α n block
  let (n', newBlock) ← match popResult with
    | .empty => pure (n, block) -- we only get .empty if the original was .empty
    | .done newBlock => pure (n, newBlock)
    | .shrink newBlock newN => pure (newN, newBlock)
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [u]) α n' newBlock
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Array [u]) α) e rhs
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

/-- Given `x : FullBlock α n` and `idx : Nat`, returns `x.get idx`. -/
def fullBlockGet (x : Expr) (n : Nat) (idx : Nat) : OptionT Id Expr := do
  match n with
  | 0 =>
    let_expr FullBlock.single _ val := x | failure
    return val
  | k + 1 =>
    let_expr FullBlock.split _ _ l r := x | failure
    fullBlockGet (if idx.testBit k then r else l) k idx

/-- Given `x : PartialBlock α n` and `idx : Nat`, returns `x.get? idx`. -/
partial def partialBlockGet (x : Expr) (idx : Nat) : OptionT Id (Option Expr) :=
  match_expr x with
  | PartialBlock.empty _ => return none
  | PartialBlock.split _ n _ l r _ => do
    let some n := n.rawNatLit? | failure
    if idx < 1 <<< n then
      fullBlockGet l n idx
    else
      partialBlockGet r (idx - 1 <<< n)
  | _ => failure

builtin_cbv_simproc cbv_eval simpArrayGetInternal (Array.getInternal _ _ _) := fun e => do
  let_expr Array.getInternal _ xs idx hbounds := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some (some res) ← (partialBlockGet block idxVal).run | return .rfl
  let some := mkApp2 (.const ``some [u]) α res
  let someRefl := mkApp2 (.const ``Eq.refl [u.succ]) (.app (.const ``Option [u]) α) some
  let proof := mkApp7 (.const ``PartialBlock.getElem_toArray_of_eq_some [u])
    α n block idx res someRefl hbounds
  return .step res proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayGet!Internal (Array.get!Internal _ _) := fun e => do
  let_expr Array.get!Internal _ inhabited xs idx := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some (some res) ← (partialBlockGet block idxVal).run | return .rfl
  let some := mkApp2 (.const ``some [u]) α res
  let someRefl := mkApp2 (.const ``Eq.refl [u.succ]) (.app (.const ``Option [u]) α) some
  let proof := mkApp7 (.const ``PartialBlock.getElem!_toArray_of_eq_some [u])
    α inhabited n block idx res someRefl
  return .step res proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayGetElem ((_ : Array _)[_]) := fun e => do
  let_expr getElem _ _ _ _ _ xs idx hbounds := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some (some res) ← (partialBlockGet block idxVal).run | return .rfl
  let some := mkApp2 (.const ``some [u]) α res
  let someRefl := mkApp2 (.const ``Eq.refl [u.succ]) (.app (.const ``Option [u]) α) some
  let proof := mkApp7 (.const ``PartialBlock.getElem_toArray_of_eq_some [u])
    α n block idx res someRefl hbounds
  return .step res proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayGetElem! ((_ : Array _)[_]!) := fun e => do
  let_expr getElem! _ _ _ _ _ inhabited xs idx := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some (some res) ← (partialBlockGet block idxVal).run | return .rfl
  let some := mkApp2 (.const ``some [u]) α res
  let someRefl := mkApp2 (.const ``Eq.refl [u.succ]) (.app (.const ``Option [u]) α) some
  let proof := mkApp7 (.const ``PartialBlock.getElem!_toArray_of_eq_some [u])
    α inhabited n block idx res someRefl
  return .step res proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayGetElem? ((_ : Array _)[_]?) := fun e => do
  let_expr getElem? _ _ _ _ _ xs idx := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some res ← (partialBlockGet block idxVal).run | return .rfl
  let rhs := match res with
    | some res => mkApp2 (.const ``some [u]) α res
    | none => .app (.const ``none [u]) α
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Option [u]) α) e rhs
  let proof := mkApp4 (.const ``PartialBlock.getElem?_toArray [u]) α n block idx
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

/-- Given `x : FullBlock α n` and `idx : Nat`, returns `x.modify idx f`. -/
@[specialize]
def fullBlockModify (x : Expr) (n : Nat) (idx : Nat) (op : Expr → Expr) :
    OptionT Sym.SymM Expr := do
  match n with
  | 0 =>
    let_expr FullBlock.single _ val := x | failure
    mkAppS x.appFn! (op val)
  | k + 1 =>
    let_expr FullBlock.split _ _ l r := x | failure
    if idx.testBit k then
      mkAppS x.appFn! (← fullBlockModify r k idx op)
    else
      mkAppS₂ x.appFn!.appFn! (← fullBlockModify l k idx op) r

/-- Given `x : PartialBlock α n` and `idx : Nat`, returns `x.modify f idx`. -/
@[specialize]
partial def partialBlockModify (x : Expr) (idx : Nat) (op : Expr → Expr) :
    OptionT Sym.SymM Expr :=
  match_expr x with
  | PartialBlock.empty _ => return x
  | PartialBlock.split _ n _ l r h => do
    let some n := n.rawNatLit? | failure
    if idx < 1 <<< n then
      mkAppS₃ (x.getBoundedAppFn 3) (← fullBlockModify l n idx op) r h
    else
      mkAppS₂ (x.getBoundedAppFn 2) (← partialBlockModify r (idx - 1 <<< n) op) h
  | _ => failure

/-- Given `x : FullBlock α n`, returns `x.map f`. -/
partial def fullBlockMap (ctx : ArrayBuilderCtx) (x : Expr) (f : Expr) :
    StateT (Std.HashMap Sym.ExprPtr Expr) (OptionT Sym.SymM) Expr := do
  if let some res := (← get)[Sym.ExprPtr.mk x]? then
    return res
  match_expr x with
  | FullBlock.single _ val =>
    let res ← ctx.fullSingle (f.app val)
    modify fun cache => cache.insert (Sym.ExprPtr.mk x) res
    return res
  | FullBlock.split _ n l r =>
    let res ← ctx.fullSplit n (← fullBlockMap ctx l f) (← fullBlockMap ctx r f)
    modify fun cache => cache.insert (Sym.ExprPtr.mk x) res
    return res
  | _ => failure

/-- Given `x : PartialBlock α n` and `idx : Nat`, returns `x.modify f idx`. -/
partial def partialBlockMap (ctx : ArrayBuilderCtx) (x : Expr) (f : Expr) :
    StateT (Std.HashMap Sym.ExprPtr Expr) (OptionT Sym.SymM) Expr := do
  match_expr x with
  | PartialBlock.empty _ => return ctx.partialEmpty
  | PartialBlock.split _ n m l r _ =>
    ctx.partialSplit n m (← fullBlockMap ctx l f) (← partialBlockMap ctx r f)
  | _ => failure

def fullBlockSingleCongr {nm} (u : Level) (α : Expr) (val : Expr) (x : Expr)
    (_h : x = mkApp2 (.const nm [u]) α val) (valRes : Sym.Simp.Result) :
    Sym.SymM Sym.Simp.Result :=
  match valRes with
  | res@(.rfl ..) => return res
  | .step val' proof _ cd =>
    let fullBlockZero := mkApp2 (.const ``FullBlock [u]) α (.lit (.natVal 0))
    let proof := mkApp6 (.const ``congrArg [u.succ, u.succ])
      α fullBlockZero val val' x.appFn! proof
    return .step (← mkAppS x.appFn! val') proof (done := true) cd

def toArrayCongr (u : Level) (α : Expr) (n : Expr) (val : Expr) (x : Expr)
    (valRes : Sym.Simp.Result) : Sym.SymM Sym.Simp.Result :=
  match valRes with
  | res@(.rfl ..) => return res
  | .step val' proof _ cd =>
    let partialBlock := mkApp2 (.const ``PartialBlock [u]) α n
    let array := .app (.const ``Array [u]) α
    let proof := mkApp6 (.const ``congrArg [u.succ, u.succ])
      partialBlock array val val' x.appFn! proof
    return .step (← mkAppS x.appFn! val') proof (done := true) cd

def fullBlockSplitCongr {nm} (u : Level) (α : Expr) (n : Expr) (nval : Nat)
    (l r : Expr) (x : Expr) (_h : x = mkApp4 (.const nm [u]) α n l r)
    (lres rres : Sym.Simp.Result) : Sym.SymM Sym.Simp.Result :=
  letI fullBlockSmaller := mkApp2 (.const ``FullBlock [u]) α n
  letI fullBlockSelf := mkApp2 (.const ``FullBlock [u]) α (.lit (.natVal (nval + 1)))
  letI fullBlockFun := .forallE `_ fullBlockSmaller fullBlockSelf .default
  let f := x.appFn!.appFn!
  match lres, rres with
  | .rfl _ cd₁, .rfl _ cd₂ => return mkRflResult (done := true) (cd₁ || cd₂)
  | .rfl _ cd₁, .step r' proof _ cd₂ =>
    let proof := mkApp6 (.const ``congrArg [u.succ, u.succ])
      fullBlockSmaller fullBlockSelf r r' x.appFn! proof
    return .step (← mkAppS x.appFn! r') proof (done := true) (cd₁ || cd₂)
  | .step l' proof _ cd₁, .rfl _ cd₂ =>
    let proof := mkApp6 (.const ``congrArg [u.succ, u.succ])
      fullBlockSmaller fullBlockFun l l' f proof
    let proof := mkApp6 (.const ``congrFun' [u.succ, u.succ])
      fullBlockSmaller fullBlockSelf (f.app l) (f.app l') proof r
    return .step (← mkAppS₂ f l' r) proof (done := true) (cd₁ || cd₂)
  | .step l' lproof _ cd₁, .step r' rproof _ cd₂ =>
    let proof := mkApp6 (.const ``congrArg [u.succ, u.succ])
      fullBlockSmaller fullBlockFun l l' f lproof
    let proof := mkApp8 (.const ``congr [u.succ, u.succ])
      fullBlockSmaller fullBlockSelf (f.app l) (f.app l') r r' proof rproof
    return .step (← mkAppS₂ f l' r') proof (done := true) (cd₁ || cd₂)

def partialBlockSplitCongr {nm} (u : Level) (α : Expr) (n m : Expr)
    (l r : Expr) (h : Expr) (x : Expr) (_h : x = mkApp6 (.const nm [u]) α n m l r h)
    (lres rres : Sym.Simp.Result) : Sym.SymM Sym.Simp.Result :=
  let useCongrSimp (l' r' : Expr) (lproof rproof : Option Expr) (cd : Bool) : Sym.SymM Result := do
    let lproof := lproof.getD (mkApp2 (.const ``Eq.refl [u.succ]) (mkApp2 (.const ``FullBlock [u]) α n) l)
    let rproof := rproof.getD (mkApp2 (.const ``Eq.refl [u.succ]) (mkApp2 (.const ``PartialBlock [u]) α m) r)
    let proof := mkApp10 (.const ``PartialBlock.split.congr_simp [u])
      α n m l l' lproof r r' rproof h
    let f := x.getBoundedAppFn 3
    return .step (← mkAppS₃ f l' r' h) proof (done := true) cd
  match lres, rres with
  | .rfl _ cd₁, .rfl _ cd₂ => return mkRflResult (done := true) (cd₁ || cd₂)
  | .rfl _ cd₁, .step r' proof _ cd₂ => useCongrSimp l r' none proof (cd₁ || cd₂)
  | .step l' proof _ cd₁, .rfl _ cd₂ => useCongrSimp l' r proof none (cd₁ || cd₂)
  | .step l' lproof _ cd₁, .step r' rproof _ cd₂ => useCongrSimp l' r' lproof rproof (cd₁ || cd₂)

def targetedFullSimp (x : Expr) (n : Nat) (idx : Nat) : SimpM Result := do
  match n with
  | 0 =>
    let (eq := heq) mkApp2 (.const nm [u]) α val := x | return .rfl (done := true)
    unless nm == ``FullBlock.single do return .rfl (done := true)
    fullBlockSingleCongr u α val x heq (← simp val)
  | k + 1 =>
    let (eq := heq) mkApp4 (.const nm [u]) α n l r := x | return .rfl (done := true)
    unless nm == ``FullBlock.split do return .rfl (done := true)
    if idx.testBit k then
      fullBlockSplitCongr u α n k l r x heq .rfl (← targetedFullSimp r k (idx - 1 <<< k))
    else
      fullBlockSplitCongr u α n k l r x heq (← targetedFullSimp l k idx) .rfl

partial def targetedPartialSimp (x : Expr) (idx : Nat) : SimpM Result := do
  match heq : x with
  | mkApp6 (.const nm [u]) α n m l r h =>
    unless nm == ``PartialBlock.split do return .rfl (done := true)
    let some nval := n.rawNatLit? | return .rfl (done := true)
    if idx < 1 <<< nval then
      let leftRes ← targetedFullSimp l nval idx
      partialBlockSplitCongr u α n m l r h x heq leftRes .rfl
    else
      let rightRes ← targetedPartialSimp r (idx - 1 <<< nval)
      partialBlockSplitCongr u α n m l r h x heq .rfl rightRes
  | _ => return .rfl (done := true) -- including PartialBlock.empty

def completeFullSimp (x : Expr) : StateT (Std.HashMap Sym.ExprPtr Result) SimpM Result := do
  if let some res := (← get)[Sym.ExprPtr.mk x]? then
    return res
  match heq : x with
  | mkApp2 (.const nm [u]) α val =>
    unless nm == ``FullBlock.single do return .rfl (done := true)
    let res ← fullBlockSingleCongr u α val x heq (← simp val)
    modify fun cache => cache.insert (Sym.ExprPtr.mk x) res
    return res
  | mkApp4 (.const nm [u]) α n l r =>
    unless nm == ``FullBlock.split do return .rfl (done := true)
    let some k := n.rawNatLit? | return .rfl (done := true)
    let res ← fullBlockSplitCongr u α n k l r x heq (← completeFullSimp l) (← completeFullSimp r)
    modify fun cache => cache.insert (Sym.ExprPtr.mk x) res
    return res
  | _ => return .rfl (done := true)

partial def completePartialSimp (x : Expr) :
    StateT (Std.HashMap Sym.ExprPtr Result) SimpM Result := do
  match heq : x with
  | mkApp6 (.const nm [u]) α n m l r h =>
    unless nm == ``PartialBlock.split do return .rfl (done := true)
    let leftRes ← completeFullSimp l
    let rightRes ← completePartialSimp r
    partialBlockSplitCongr u α n m l r h x heq leftRes rightRes
  | _ => return .rfl (done := true) -- including PartialBlock.empty

builtin_cbv_simproc cbv_eval simpArraySet (Array.set _ _ _ _) := fun e => do
  let_expr Array.set _ xs idx val hbounds := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some newBlock ← (partialBlockModify block idxVal fun _ => val).run | return .rfl
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [u]) α n newBlock
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Array [u]) α) e rhs
  let proof := mkApp6 (.const ``PartialBlock.set_toArray [u]) α n block idx val hbounds
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

builtin_cbv_simproc cbv_eval simpArraySetIfInBounds (Array.setIfInBounds _ _ _) := fun e => do
  let_expr Array.setIfInBounds _ xs idx val := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some newBlock ← (partialBlockModify block idxVal fun _ => val).run | return .rfl
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [u]) α n newBlock
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Array [u]) α) e rhs
  let proof := mkApp5 (.const ``PartialBlock.setIfInBounds_toArray [u]) α n block idx val
  let proof := mkExpectedPropHint proof eq
  return .step rhs proof (done := true)

builtin_cbv_simproc cbv_eval simpArrayModify (Array.modify _ _ _) := fun e => do
  let_expr Array.modify _ xs idx fn := e | return .rfl
  let_expr c@PartialBlock.toArray α n block := xs | return .rfl
  let some idxVal := Sym.getNatValue? idx | return .rfl
  let u : Level := c.constLevels![0]!
  let some newBlock ← (partialBlockModify block idxVal fn.app).run | return .rfl
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [u]) α n newBlock
  let eq := mkApp3 (.const ``Eq [u.succ]) (.app (.const ``Array [u]) α) e rhs
  let proof := mkApp5 (.const ``PartialBlock.modify_toArray [u]) α n block idx fn
  let proof := mkExpectedPropHint proof eq
  mkEqTransResult e rhs proof (← toArrayCongr u α n newBlock rhs (← targetedPartialSimp newBlock idxVal))

builtin_cbv_simproc cbv_eval simpArrayMap (Array.map _ _) := fun e => do
  let_expr c@Array.map _ β fn xs := e | return .rfl
  let_expr PartialBlock.toArray α n block := xs | return .rfl
  let [u, v] := c.constLevels! | return .rfl
  let builderCtx ← ArrayBuilderCtx.mk v β
  let some newBlock ← (partialBlockMap builderCtx block fn).run' {} |>.run |
    trace[debug] "Failed to map block at{indentExpr block}"
    return .rfl
  let rhs ← mkAppS₃ (← mkConstS ``PartialBlock.toArray [v]) β n newBlock
  let eq := mkApp3 (.const ``Eq [v.succ]) (.app (.const ``Array [v]) β) e rhs
  let proof := mkApp5 (.const ``PartialBlock.map_toArray [u, v]) α β n block fn
  let proof := mkExpectedPropHint proof eq
  mkEqTransResult e rhs proof (← toArrayCongr v β n newBlock rhs (← (completePartialSimp newBlock).run' {}))

/-
/-- Reduce `#[...][n]` for literal arrays and literal `Nat` indices. -/
builtin_cbv_simproc cbv_eval simpArrayGetElem (@GetElem.getElem (Array _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs n _ := e | return .rfl
  let some elems := getArrayLitElems? xs | return .rfl
  let some idx := Sym.getNatValue? n | return .rfl
  if h : idx < elems.size then
    let result := elems[idx]
    return .step result (← Sym.mkEqRefl result)
  else
    return .rfl

/-- Reduce `#[...][n]?` for literal arrays and literal `Nat` indices. -/
builtin_cbv_simproc cbv_eval simpArrayGetElem? (@GetElem?.getElem? (Array _) Nat _ _ _ _ _) := fun e => do
  let_expr GetElem?.getElem? _ _ α _ _ xs n := e | return .rfl
  let some elems := getArrayLitElems? xs | return .rfl
  let some idx := Sym.getNatValue? n | return .rfl
  let sortLevel ← Sym.getLevel α
  let .succ u := sortLevel | return .rfl
  let result ←
    if h : idx < elems.size then
      Sym.share <| mkApp2 (mkConst ``Option.some [u]) α elems[idx]
    else
      Sym.share <| mkApp (mkConst ``Option.none [u]) α
  return .step result (← Sym.mkEqRefl result)
-/

end Lean.Meta.Tactic.Cbv
