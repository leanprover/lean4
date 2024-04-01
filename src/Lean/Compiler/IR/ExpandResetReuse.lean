/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Anton Lorenzen
-/
prelude
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.FreeVars

namespace Lean.IR.ExpandResetReuse

/-- Mapping from variable to projections.
    We use this in reuse specialization to avoid setting fields that are already set.
-/
abbrev ProjMap  := HashMap VarId Expr
namespace CollectProjMap
abbrev Collector := ProjMap → ProjMap
@[inline] def collectVDecl (x : VarId) (v : Expr) : Collector := fun m =>
  match v with
  | .proj ..  => m.insert x v
  | .sproj .. => m.insert x v
  | .uproj .. => m.insert x v
  | _         => m

partial def collectFnBody : FnBody → Collector
  | .vdecl x _ v b   => collectVDecl x v ∘ collectFnBody b
  | .jdecl _ _ v b   => collectFnBody v ∘ collectFnBody b
  | .case _ _ _ alts => fun s => alts.foldl (fun s alt => collectFnBody alt.body s) s
  | e                => if e.isTerminal then id else collectFnBody e.body
end CollectProjMap

/-- Create a mapping from variables to projections.
   This function assumes variable ids have been normalized -/
def mkProjMap (d : Decl) : ProjMap :=
  match d with
  | .fdecl (body := b) .. => CollectProjMap.collectFnBody b {}
  | _ => {}

structure Context where
  projMap : ProjMap

abbrev Mask := Array (Option VarId)

/-- Auxiliary function for eraseProjIncFor.
    Traverse bs left to right to find pairs of
    ```
    let z := proj[i] y
    inc z n c
    ```
    If `n=1` remove the `inc` instruction and if `n>1` replace `inc z n c` with `inc z (n-1) c`.
    Additionally, we track the variables `z` that have been found in the mask.
-/
partial def eraseProjIncForAux (y : VarId) (bs : Array FnBody) (mask : Mask) (keep : Array FnBody) : Array FnBody × Mask :=
  let done (_ : Unit)        := (bs ++ keep.reverse, mask)
  let keepInstr (b : FnBody) := eraseProjIncForAux y bs.pop mask (keep.push b)
  if bs.size < 2 then done ()
  else
    let b := bs.back
    match b with
    | .vdecl _ _ (.sproj _ _ _) _ => keepInstr b
    | .vdecl _ _ (.uproj _ _) _   => keepInstr b
    | .inc z n c p _ =>
      if n == 0 then done () else
      let b' := bs[bs.size - 2]!
      match b' with
      | .vdecl w _ (.proj i x) _ =>
        if w == z && y == x then
          /- Found
             ```
             let z := proj[i] y
             inc z n c
             ```
             We keep `proj`, and `inc` when `n > 1`
          -/
          let bs   := bs.pop.pop
          let mask := mask.set! i (some z)
          let keep := keep.push b'
          let keep := if n == 1 then keep else keep.push (FnBody.inc z (n-1) c p FnBody.nil)
          eraseProjIncForAux y bs mask keep
        else done ()
      | _ => done ()
    | _ => done ()

/-- Try to erase one `inc` instruction on projections of `y` occurring in the tail of `bs`.
   Return the updated `bs` and a bit mask specifying which `inc`s have been removed. -/
def eraseProjIncFor (n : Nat) (y : VarId) (bs : Array FnBody) : Array FnBody × Mask :=
  eraseProjIncForAux y bs (mkArray n none) #[]

abbrev M := ReaderT Context (StateM Nat)
  def mkFresh : M VarId :=
    modifyGet fun n => ({ idx := n }, n + 1)
  def mkFreshJoinPoint : M JoinPointId :=
    modifyGet fun n => ({ idx := n }, n + 1)

/-- If the reused cell is unique, we can reuse its memory.
    Then we have to manually release all fields that are not live. -/
def releaseUnreadFields (y : VarId) (mask : Mask) : M (FnBody → FnBody) :=
  mask.size.foldM (init := id) fun i b =>
    match mask.get! i with
    | some _ => pure b -- code took ownership of this field
    | none   => do
      let fld ← mkFresh
      pure (FnBody.vdecl fld IRType.object (Expr.proj i y) ∘ (FnBody.dec fld 1 true false ∘ b))

/-- Given `set x[i] := y`, return true iff `y := proj[i] x` -/
def isSelfSet (ctx : Context) (x : VarId) (i : Nat) (y : Arg) : Bool :=
  match y with
  | Arg.var y =>
    match ctx.projMap.find? y with
    | some (Expr.proj j w) => j == i && w == x
    | _ => false
  | _ => false

/-- Set fields of `y` to `zs`. We avoid assignments that are already set. -/
def setFields (ctx : Context) (y : VarId) (zs : Array Arg) (b : FnBody) : FnBody :=
  zs.size.fold (init := b) fun i b =>
    if isSelfSet ctx y i (zs.get! i) then b
    else FnBody.set y i (zs.get! i) b

/-- Given `uset x[i] := y`, return true iff `y := uproj[i] x` -/
def isSelfUSet (ctx : Context) (x : VarId) (i : Nat) (y : VarId) : Bool :=
  match ctx.projMap.find? y with
  | some (Expr.uproj j w) => j == i && w == x
  | _                     => false

/-- Given `sset x[n, i] := y`, return true iff `y := sproj[n, i] x` -/
def isSelfSSet (ctx : Context) (x : VarId) (n : Nat) (i : Nat) (y : VarId) : Bool :=
  match ctx.projMap.find? y with
  | some (Expr.sproj m j w) => n == m && j == i && w == x
  | _                       => false

/-- The empty reuse token returned for non-unique cells. -/
def null := Expr.lit (LitVal.num 0)

/-- Create a new join point, where the declaration `v` obtains a function that will generate
    a jump to the join point with the variable as an argument. We optimize the case, where
    the binding is just a return and float it into the declaration. -/
def mkJoin (x : VarId) (t : IRType) (b : FnBody) (v : (VarId → FnBody) → FnBody) : M FnBody :=
  match b with
  | FnBody.ret _ =>
      return v fun z => FnBody.ret (Arg.var z)
  | _ => do
    let j ← mkFreshJoinPoint
    let z ← mkFresh
    -- We use the given VarId for the joinpoint, which avoids the need to rename the tokens.
    -- This is especially important since otherwise the ProjectionMap would find projections
    -- out of the old variables and thus break reuse specialization.
    return FnBody.jdecl j #[mkParam z false t]
      (b.replaceVar x z)
      (v (fun z => mkJmp j #[Arg.var z]))

/-- Reuse specialization. -/
def specializeReuse (reused token : VarId) (c : CtorInfo) (u : Bool) (t : IRType) (xs : Array Arg) (b : FnBody) : M FnBody := do
  let ctx ← read
  let null? ← mkFresh
  let newAlloc ← mkFresh
  mkJoin reused t b fun jmp =>
    (FnBody.vdecl null? IRType.uint8 (Expr.isNull token)
      (mkIf null?
        (FnBody.vdecl newAlloc t (Expr.ctor c xs)
          (jmp newAlloc))
        ((if u then FnBody.setTag token c.cidx else id)
          (setFields ctx token xs
            (jmp token)))))

/-- Increment all live children and decrement y. -/
def adjustReferenceCountsSlowPath (y : VarId) (mask : Mask) (b : FnBody) :=
  let b := FnBody.dec y 1 true false b
  mask.foldl (init := b) fun b m => match m with
      | some z => FnBody.inc z 1 true false b
      | none   => b

/- Drop specialization -/
def specializeReset (token oldAlloc : VarId) (mask : Mask) (b : FnBody) : M FnBody := do
  let shared? ← mkFresh
  let z2 ← mkFresh
  let fastPath ← releaseUnreadFields oldAlloc mask
  mkJoin token IRType.object b fun jmp =>
    (FnBody.vdecl shared? IRType.uint8 (Expr.isShared oldAlloc)
      (mkIf shared?
        (adjustReferenceCountsSlowPath oldAlloc mask
          (FnBody.vdecl z2 IRType.object null
            (jmp z2)))
        (fastPath (jmp oldAlloc))))

partial def searchAndSpecialize : FnBody → Array FnBody → Array VarId → M FnBody
  | FnBody.vdecl x _ (Expr.reset n y) b, bs, tokens => do
      let (bs, mask) := eraseProjIncFor n y bs
      let b ← searchAndSpecialize b #[] (tokens.push x)
      let b ← specializeReset x y mask b
      return reshape bs b
  | FnBody.vdecl z t (Expr.reuse w c u zs) b, bs, tokens => do
      let b ← searchAndSpecialize b #[] tokens
      let b ← specializeReuse z w c u t zs b
      return reshape bs b
  | FnBody.dec z n c p b, bs, tokens =>
      if Array.contains tokens z then return FnBody.del z b
    else do
      let b ← searchAndSpecialize b #[] tokens
      return reshape bs (FnBody.dec z n c p b)
  | FnBody.jdecl j xs v b, bs, tokens => do
    let v ← searchAndSpecialize v #[] tokens
    let b ← searchAndSpecialize b #[] tokens
    return reshape bs (FnBody.jdecl j xs v b)
  | FnBody.case tid x xType alts, bs, tokens => do
    let alts ← alts.mapM fun alt => alt.mmodifyBody fun b => searchAndSpecialize b #[] tokens
    return reshape bs (FnBody.case tid x xType alts)
  | b, bs, tokens =>
    if b.isTerminal then return reshape bs b
    else searchAndSpecialize b.body (push bs b) tokens

def main (d : Decl) : Decl :=
  match d with
  | .fdecl (body := b) .. =>
    let m := mkProjMap d
    let nextIdx := d.maxIndex + 1
    let bNew := (searchAndSpecialize b #[] #[] { projMap := m }).run' nextIdx
    d.updateBody! bNew
  | d => d

end ExpandResetReuse

/-- (Try to) expand `reset` and `reuse` instructions. -/
def Decl.expandResetReuse (d : Decl) : Decl :=
  (ExpandResetReuse.main d).normalizeIds

end Lean.IR
