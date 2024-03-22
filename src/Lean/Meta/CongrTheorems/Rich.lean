/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.CongrTheorems.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Refl
import Lean.Class

namespace Lean.Meta

initialize registerTraceClass `Meta.CongrTheorems

/-- Generates a congruence lemma for a function `f` for `numArgs` of its arguments.
The only `Lean.Meta.CongrArgKind` kinds that appear in such a lemma
are `.eq`, `.heq`, and `.subsingletonInst`.
The resulting lemma proves either an `Eq` or a `HEq` depending on whether the types
of the LHS and RHS are equal or not.

This function is a wrapper around `Lean.Meta.mkHCongrWithArity`.
It transforms the resulting congruence lemma by trying to automatically prove hypotheses
using subsingleton lemmas, and if they are so provable they are recorded with `.subsingletonInst`.
Note that this is slightly abusing `.subsingletonInst` since
(1) the argument might not be for a `Decidable` instance and
(2) the argument might not even be an instance. -/
def mkHCongrWithArity' (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let thm ← mkHCongrWithArity f numArgs
  process thm thm.type thm.argKinds.toList #[] #[] #[]
where
  /-- Process the congruence theorem by trying to pre-prove arguments using `prove`. -/
  process (cthm : CongrTheorem) (type : Expr) (argKinds : List CongrArgKind)
      (argKinds' : Array CongrArgKind) (params args : Array Expr) : MetaM CongrTheorem := do
    match argKinds with
    | [] =>
      if params.size == args.size then
        return cthm
      else
        let pf' ← mkLambdaFVars params (mkAppN cthm.proof args)
        return {proof := pf', type := ← inferType pf', argKinds := argKinds'}
    | argKind :: argKinds =>
      match argKind with
      | .eq | .heq =>
        forallBoundedTelescope type (some 3) fun params' type' => do
          let #[x, y, eq] := params' | unreachable!
          -- See if we can prove `eq` from previous parameters.
          let g := (← mkFreshExprMVar (← inferType eq)).mvarId!
          let g ← g.clear eq.fvarId!
          if (← observing? <| prove g params).isSome then
            process cthm type' argKinds (argKinds'.push .subsingletonInst)
              (params := params ++ #[x, y]) (args := args ++ #[x, y, .mvar g])
          else
            process cthm type' argKinds (argKinds'.push argKind)
              (params := params ++ params') (args := args ++ params')
      | _ => panic! "Unexpected CongrArgKind"
  /-- Close the goal given only the fvars in `params`, or else fails. -/
  prove (g : MVarId) (params : Array Expr) : MetaM Unit := do
    -- Prune the local context.
    let g ← g.cleanup
    -- Substitute equalities that come from only this congruence lemma.
    let [g] ← g.casesRec fun localDecl => do
      return (localDecl.type.isEq || localDecl.type.isHEq) && params.contains localDecl.toExpr
      | failure
    try g.refl; return catch _ => pure ()
    try g.hrefl; return catch _ => pure ()
    if ← g.proofIrrelHeq then return
    -- Make the goal be an eq and then try `Subsingleton.elim`
    let g ← g.heqOfEq
    if ← g.subsingletonElim then return
    -- We have no more tricks.
    failure

/--
`mkRichHCongr fType funInfo fixedFun fixedParams forceHEq`
create a congruence lemma to prove that `Eq/HEq (f a₁ ... aₙ) (f' a₁' ... aₙ')`.
The functions have type `fType` and the number of arguments is governed by the `funInfo` data.
Each argument produces an `Eq/HEq aᵢ aᵢ'` hypothesis, but we also provide these hypotheses
the additional facts that the preceding equalities have been proved (unlike in `mkHCongrWithArity`).
The first two arguments of the resulting theorem are for `f` and `f'`, followed by a proof
of `f = f'`, unless `fixedFun` is `true` (see below).

When including hypotheses about previous hypotheses, we make use of dependency information
and only include relevant equalities.

The argument `fty` denotes the type of `f`. The arity of the resulting congruence lemma is
controlled by the size of the `info` array.

For the purpose of generating nicer lemmas (to help `to_additive` for example),
this function supports generating lemmas where certain parameters
are meant to be fixed:

* If `fixedFun` is `false` (the default) then the lemma starts with three arguments for `f`, `f'`,
and `h : f = f'`. Otherwise, if `fixedFun` is `true` then the lemma starts with just `f`.

* If the `fixedParams` argument has `true` for a particular argument index, then this is a hint
that the congruence lemma may use the same parameter for both sides of the equality. There is
no guarantee -- it respects it if the types are equal for that parameter (i.e., if the parameter
does not depend on non-fixed parameters).

If `forceHEq` is `true` then the conclusion of the generated theorem is a `HEq`.
Otherwise it might be an `Eq` if the equality is homogeneous.

This is the interpretation of the `CongrArgKind`s in the generated congruence theorem:
* `.eq` corresponds to having three arguments `(x : α) (x' : α) (h : x = x')`.
  Note that `h` might have additional hypotheses.
* `.heq` corresponds to having three arguments `(x : α) (x' : α') (h : HEq x x')`
  Note that `h` might have additional hypotheses.
* `.fixed` corresponds to having a single argument `(x : α)` that is fixed between the LHS and RHS
* `.subsingletonInst` corresponds to having two arguments `(x : α) (x' : α')` for which the
  congruence generator was able to prove that `HEq x x'` already. This is a slight abuse of
  this `CongrArgKind` since this is used even for types that are not subsingleton typeclasses.

Note that the first entry in this array is for the function itself.
-/
partial def mkRichHCongr (fType : Expr) (info : FunInfo)
    (fixedFun : Bool := false) (fixedParams : Array Bool := #[])
    (forceHEq : Bool := false) :
    MetaM CongrTheorem := do
  trace[Meta.CongrTheorems] "ftype: {fType}"
  trace[Meta.CongrTheorems] "deps: {info.paramInfo.map (fun p => p.backDeps)}"
  trace[Meta.CongrTheorems] "fixedFun={fixedFun}, fixedParams={fixedParams}"
  doubleTelescope fType info.getArity fixedParams fun xs ys fixedParams => do
    trace[Meta.CongrTheorems] "xs = {xs}"
    trace[Meta.CongrTheorems] "ys = {ys}"
    trace[Meta.CongrTheorems] "computed fixedParams={fixedParams}"
    let lctx := (← getLCtx) -- checkpoint for a local context that only has the parameters
    withLocalDeclD `f fType fun ef => withLocalDeclD `f' fType fun pef' => do
    let ef' := if fixedFun then ef else pef'
    withLocalDeclD `e (← mkEq ef ef') fun ee => do
    withNewEqs xs ys fixedParams fun kinds eqs => do
      let fParams := if fixedFun then #[ef] else #[ef, ef', ee]
      let mut hs := fParams     -- parameters to the basic congruence lemma
      let mut hs' := fParams    -- parameters to the richer congruence lemma
      let mut vals' := fParams  -- how to calculate the basic parameters from the richer ones
      for i in [0 : info.getArity] do
        hs := hs.push xs[i]!
        hs' := hs'.push xs[i]!
        vals' := vals'.push xs[i]!
        if let some (eq, eq', val) := eqs[i]! then
          -- Not a fixed argument
          hs := hs.push ys[i]! |>.push eq
          hs' := hs'.push ys[i]! |>.push eq'
          vals' := vals'.push ys[i]! |>.push val
      -- Generate the theorem with respect to the simpler hypotheses
      let mkConcl := if forceHEq then mkHEq else mkEqHEq
      let congrType ← mkForallFVars hs (← mkConcl (mkAppN ef xs) (mkAppN ef' ys))
      trace[Meta.CongrTheorems] "simple congrType: {congrType}"
      let some proof ← withLCtx lctx (← getLocalInstances) <| trySolve congrType
        | throwError "Internal error when constructing congruence lemma proof"
      -- At this point, `mkLambdaFVars hs' (mkAppN proof vals')` is the richer proof.
      -- We try to precompute some of the arguments using `trySolve`.
      let mut hs'' := #[] -- eq' parameters that are actually used beyond those in `fParams`
      let mut pfVars := #[] -- eq' parameters that can be solved for already
      let mut pfVals := #[] -- the values to use for these parameters
      let mut kinds' : Array CongrArgKind := #[if fixedFun then .fixed else .eq]
      for i in [0 : info.getArity] do
        hs'' := hs''.push xs[i]!
        if let some (_, eq', _) := eqs[i]! then
          -- Not a fixed argument
          hs'' := hs''.push ys[i]!
          let pf? ← withLCtx lctx (← getLocalInstances) <| trySolve (← inferType eq')
          if let some pf := pf? then
            pfVars := pfVars.push eq'
            pfVals := pfVals.push pf
            kinds' := kinds'.push .subsingletonInst
          else
            hs'' := hs''.push eq'
            kinds' := kinds'.push kinds[i]!
        else
          kinds' := kinds'.push .fixed
      trace[Meta.CongrTheorems] "CongrArgKinds: {repr kinds'}"
      -- Take `proof`, abstract the pfVars and provide the solved-for proofs (as an
      -- optimization for proof term size) then abstract the remaining variables.
      -- The `usedOnly` probably has no affect.
      -- Note that since we are doing `proof.beta vals'` there is technically some quadratic
      -- complexity, but it shouldn't be too bad since they're some applications of just variables.
      let proof' ← mkLambdaFVars fParams (← mkLambdaFVars (usedOnly := true) hs''
                    (mkAppN (← mkLambdaFVars pfVars (proof.beta vals')) pfVals))
      let congrType' ← inferType proof'
      trace[Meta.CongrTheorems] "rich congrType: {congrType'}"
      return {proof := proof', type := congrType', argKinds := kinds'}
where
  /-- Similar to doing `forallBoundedTelescope` twice, but makes use of the `fixed` array, which
  is used as a hint for whether both variables should be the same. This is only a hint though,
  since we respect it only if the binding domains are equal.
  We affix `'` to the second list of variables, and all the variables are introduced
  with default binder info. Calls `k` with the xs, ys, and a revised `fixed` array -/
  doubleTelescope {α} (fty : Expr) (numVars : Nat) (fixed : Array Bool)
      (k : Array Expr → Array Expr → Array Bool → MetaM α) : MetaM α := do
    let rec loop (i : Nat)
        (ftyx ftyy : Expr) (xs ys : Array Expr) (fixed' : Array Bool) : MetaM α := do
      if i < numVars then
        let ftyx ← whnf ftyx
        let ftyy ← whnf ftyy
        unless ftyx.isForall do
          throwError "doubleTelescope: function doesn't have enough parameters"
        withLocalDeclD ftyx.bindingName! ftyx.bindingDomain! fun fvarx => do
          let ftyx' := ftyx.bindingBody!.instantiate1 fvarx
          if fixed.getD i false && ftyx.bindingDomain! == ftyy.bindingDomain! then
            -- Fixed: use the same variable for both
            let ftyy' := ftyy.bindingBody!.instantiate1 fvarx
            loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvarx) (fixed'.push true)
          else
            -- Not fixed: use different variables
            let yname := ftyy.bindingName!.appendAfter "'"
            withLocalDeclD yname ftyy.bindingDomain! fun fvary => do
              let ftyy' := ftyy.bindingBody!.instantiate1 fvary
              loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvary) (fixed'.push false)
      else
        k xs ys fixed'
    loop 0 fty fty #[] #[] #[]
  /-- Introduce variables for equalities between the arrays of variables. Uses `fixedParams`
  to control whether to introduce an equality for each pair. The array of triples passed to `k`
  consists of (1) the simple congr lemma HEq arg, (2) the richer HEq arg, and (3) how to
  compute 1 in terms of 2. -/
  withNewEqs {α} (xs ys : Array Expr) (fixedParams : Array Bool)
      (k : Array CongrArgKind → Array (Option (Expr × Expr × Expr)) → MetaM α) : MetaM α :=
    let rec loop (i : Nat)
        (kinds : Array CongrArgKind) (eqs : Array (Option (Expr × Expr × Expr))) := do
      if i < xs.size then
        let x := xs[i]!
        let y := ys[i]!
        if fixedParams[i]! then
          loop (i+1) (kinds.push .fixed) (eqs.push none)
        else
          let deps := info.paramInfo[i]!.backDeps.filterMap (fun j => eqs[j]!)
          let eq' ← mkForallFVars (deps.map fun (eq, _, _) => eq) (← mkEqHEq x y)
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkEqHEq x y) fun h =>
          withLocalDeclD ((`e').appendIndexAfter (i+1)) eq' fun h' => do
            let v := mkAppN h' (deps.map fun (_, _, val) => val)
            let kind := if (← inferType h).eq?.isSome then .eq else .heq
            loop (i+1) (kinds.push kind) (eqs.push (h, h', v))
      else
        k kinds eqs
    loop 0 #[] #[]
  /-- Given a type that is a bunch of equalities implying a goal (for example, a basic
  congruence lemma), prove it if possible. Basic congruence lemmas should be provable by this.
  There are some extra tricks for handling arguments to richer congruence lemmas. -/
  trySolveCore (mvarId : MVarId) : MetaM Unit := do
    -- First cleanup the context since we're going to do `substEqs` and we don't want to
    -- accidentally use variables not actually used by the theorem.
    let mvarId ← mvarId.cleanup
    let (_, mvarId) ← mvarId.intros
    let mvarId := (← mvarId.substEqs).getD mvarId
    try mvarId.refl; return catch _ => pure ()
    try mvarId.hrefl; return catch _ => pure ()
    if ← mvarId.proofIrrelHeq then return
    -- Make the goal be an eq and then try `Subsingleton.elim`
    let mvarId ← mvarId.heqOfEq
    if ← mvarId.subsingletonElim then return
    -- We have no more tricks.
    throwError "was not able to solve for proof"
  /-- Driver for `trySolveCore`. -/
  trySolve (ty : Expr) : MetaM (Option Expr) := observing? do
    let mvar ← mkFreshExprMVar ty
    trace[Meta.CongrTheorems] "trySolve {mvar.mvarId!}"
    -- The proofs we generate shouldn't require unfolding anything.
    withReducible <| trySolveCore mvar.mvarId!
    trace[Meta.CongrTheorems] "trySolve success!"
    let pf ← instantiateMVars mvar
    return pf

end Lean.Meta
