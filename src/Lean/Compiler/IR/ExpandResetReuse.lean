/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.FreeVars

namespace Lean.IR.ExpandResetReuse
/-- Mapping from variable to projections -/
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

/-- Return true iff `x` is consumed in all branches of the current block.
   Here consumption means the block contains a `dec x` or `reuse x ...`. -/
partial def consumed (x : VarId) : FnBody → Bool
  | .vdecl _ _ v b   =>
    match v with
    | Expr.reuse y _ _ _ => x == y || consumed x b
    | _                  => consumed x b
  | .dec y _ _ _ b   => x == y || consumed x b
  | .case _ _ _ alts => alts.all fun alt => consumed x alt.body
  | e => !e.isTerminal && consumed x e.body

abbrev Mask := Array (Option VarId)

/-- Auxiliary function for eraseProjIncFor -/
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

/-- Try to erase `inc` instructions on projections of `y` occurring in the tail of `bs`.
   Return the updated `bs` and a bit mask specifying which `inc`s have been removed. -/
def eraseProjIncFor (n : Nat) (y : VarId) (bs : Array FnBody) : Array FnBody × Mask :=
  eraseProjIncForAux y bs (mkArray n none) #[]

/-- Replace `reuse x ctor ...` with `ctor ...`, and remove `dec x` -/
partial def reuseToCtor (x : VarId) : FnBody → FnBody
  | FnBody.dec y n c p b   =>
    if x == y then b -- n must be 1 since `x := reset ...`
    else FnBody.dec y n c p (reuseToCtor x b)
  | FnBody.vdecl z t v b   =>
    match v with
    | Expr.reuse y c _ xs =>
      if x == y then FnBody.vdecl z t (Expr.ctor c xs) b
      else FnBody.vdecl z t v (reuseToCtor x b)
    | _ =>
      FnBody.vdecl z t v (reuseToCtor x b)
  | FnBody.case tid y yType alts   =>
    let alts := alts.map fun alt => alt.modifyBody (reuseToCtor x)
    FnBody.case tid y yType alts
  | e =>
    if e.isTerminal then
      e
    else
      let (instr, b) := e.split
      let b := reuseToCtor x b
      instr.setBody b

/--
replace
```
x := reset y; b
```
with
```
inc z_1; ...; inc z_i; dec y; b'
```
where `z_i`'s are the variables in `mask`,
and `b'` is `b` where we removed `dec x` and replaced `reuse x ctor_i ...` with `ctor_i ...`.
-/
def mkSlowPath (x y : VarId) (mask : Mask) (b : FnBody) : FnBody :=
  let b := reuseToCtor x b
  let b := FnBody.dec y 1 true false b
  mask.foldl (init := b) fun b m => match m with
      | some z => FnBody.inc z 1 true false b
      | none   => b

abbrev M := ReaderT Context (StateM Nat)
  def mkFresh : M VarId :=
  modifyGet fun n => ({ idx := n }, n + 1)

def releaseUnreadFields (y : VarId) (mask : Mask) (b : FnBody) : M FnBody :=
  mask.size.foldM (init := b) fun i b =>
    match mask.get! i with
    | some _ => pure b -- code took ownership of this field
    | none   => do
      let fld ← mkFresh
      pure (FnBody.vdecl fld IRType.object (Expr.proj i y) (FnBody.dec fld 1 true false b))

def setFields (y : VarId) (zs : Array Arg) (b : FnBody) : FnBody :=
  zs.size.fold (init := b) fun i b => FnBody.set y i (zs.get! i) b

/-- Given `set x[i] := y`, return true iff `y := proj[i] x` -/
def isSelfSet (ctx : Context) (x : VarId) (i : Nat) (y : Arg) : Bool :=
  match y with
  | Arg.var y =>
    match ctx.projMap.find? y with
    | some (Expr.proj j w) => j == i && w == x
    | _ => false
  | _ => false

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

/-- Remove unnecessary `set/uset/sset` operations -/
partial def removeSelfSet (ctx : Context) : FnBody → FnBody
  | FnBody.set x i y b   =>
    if isSelfSet ctx x i y then removeSelfSet ctx b
    else FnBody.set x i y (removeSelfSet ctx b)
  | FnBody.uset x i y b   =>
    if isSelfUSet ctx x i y then removeSelfSet ctx b
    else FnBody.uset x i y (removeSelfSet ctx b)
  | FnBody.sset x n i y t b   =>
    if isSelfSSet ctx x n i y then removeSelfSet ctx b
    else FnBody.sset x n i y t (removeSelfSet ctx b)
  | FnBody.case tid y yType alts   =>
    let alts := alts.map fun alt => alt.modifyBody (removeSelfSet ctx)
    FnBody.case tid y yType alts
  | e =>
    if e.isTerminal then e
    else
      let (instr, b) := e.split
      let b := removeSelfSet ctx b
      instr.setBody b

partial def reuseToSet (ctx : Context) (x y : VarId) : FnBody → FnBody
  | FnBody.dec z n c p b   =>
    if x == z then FnBody.del y b
    else FnBody.dec z n c p (reuseToSet ctx x y b)
  | FnBody.vdecl z t v b   =>
    match v with
    | Expr.reuse w c u zs =>
      if x == w then
        let b := setFields y zs (b.replaceVar z y)
        let b := if u then FnBody.setTag y c.cidx b else b
        removeSelfSet ctx b
      else FnBody.vdecl z t v (reuseToSet ctx x y b)
    | _ => FnBody.vdecl z t v (reuseToSet ctx x y b)
  | FnBody.case tid z zType alts   =>
    let alts := alts.map fun alt => alt.modifyBody (reuseToSet ctx x y)
    FnBody.case tid z zType alts
  | e =>
    if e.isTerminal then e
    else
      let (instr, b) := e.split
      let b := reuseToSet ctx x y b
      instr.setBody b

/--
replace
```
x := reset y; b
```
with
```
let f_i_1 := proj[i_1] y;
...
let f_i_k := proj[i_k] y;
b'
```
where `i_j`s are the field indexes
that the code did not touch immediately before the reset.
That is `mask[j] == none`.
`b'` is `b` where `y` `dec x` is replaced with `del y`,
and `z := reuse x ctor_i ws; F` is replaced with
`set x i ws[i]` operations, and we replace `z` with `x` in `F`
-/
def mkFastPath (x y : VarId) (mask : Mask) (b : FnBody) : M FnBody := do
  let ctx ← read
  let b := reuseToSet ctx x y b
  releaseUnreadFields y mask b

-- Expand `bs; x := reset[n] y; b`
partial def expand (mainFn : FnBody → Array FnBody → M FnBody)
    (bs : Array FnBody) (x : VarId) (n : Nat) (y : VarId) (b : FnBody) : M FnBody := do
  let (bs, mask) := eraseProjIncFor n y bs
  /- Remark: we may be duplicating variable/JP indices. That is, `bSlow` and `bFast` may
     have duplicate indices. We run `normalizeIds` to fix the ids after we have expand them. -/
  let bSlow      := mkSlowPath x y mask b
  let bFast ← mkFastPath x y mask b
  /- We only optimize recursively the fast. -/
  let bFast ← mainFn bFast #[]
  let c ← mkFresh
  let b := FnBody.vdecl c IRType.uint8 (Expr.isShared y) (mkIf c bSlow bFast)
  return reshape bs b

partial def searchAndExpand : FnBody → Array FnBody → M FnBody
  | d@(FnBody.vdecl x _ (Expr.reset n y) b), bs =>
    if consumed x b then do
      expand searchAndExpand bs x n y b
    else
      searchAndExpand b (push bs d)
  | FnBody.jdecl j xs v b,   bs => do
    let v ← searchAndExpand v #[]
    searchAndExpand b (push bs (FnBody.jdecl j xs v FnBody.nil))
  | FnBody.case tid x xType alts,   bs => do
    let alts ← alts.mapM fun alt => alt.mmodifyBody fun b => searchAndExpand b #[]
    return reshape bs (FnBody.case tid x xType alts)
  | b, bs =>
    if b.isTerminal then return reshape bs b
    else searchAndExpand b.body (push bs b)

def main (d : Decl) : Decl :=
  match d with
  | .fdecl (body := b) .. =>
    let m := mkProjMap d
    let nextIdx := d.maxIndex + 1
    let bNew := (searchAndExpand b #[] { projMap := m }).run' nextIdx
    d.updateBody! bNew
  | d => d

end ExpandResetReuse

/-- (Try to) expand `reset` and `reuse` instructions. -/
def Decl.expandResetReuse (d : Decl) : Decl :=
  (ExpandResetReuse.main d).normalizeIds

end Lean.IR
