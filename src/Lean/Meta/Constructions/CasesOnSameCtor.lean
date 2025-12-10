/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
import Lean.Meta.CompletionName
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Elab.App
import Lean.Meta.SameCtorUtils

/-!
See `mkCasesOnSameCtor` below.
-/

namespace Lean

open Meta

/--
Helper for `mkCasesOnSameCtor` that constructs a heterogeneous matcher (indices may differ)
and does not include the equality proof in the motive (so it's not a the shape of a matcher) yet.
-/
public def mkCasesOnSameCtorHet (declName : Name) (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallBoundedTelescope casesOnInfo.type info.numParams fun params t =>
    forallBoundedTelescope t (some 1) fun _ t => -- ignore motive
    forallBoundedTelescope t (some (info.numIndices + 1)) fun ism1 _ =>
    forallBoundedTelescope t (some (info.numIndices + 1)) fun ism2 _ => do
      let motiveType ← mkForallFVars (ism1 ++ ism2) (mkSort v)
      withLocalDecl `motive .implicit motiveType fun motive => do

      let altTypes ← info.ctors.toArray.mapIdxM fun i ctorName => do
        let ctor := mkAppN (mkConst ctorName us) params
        let ctorType ← inferType ctor
        forallTelescope ctorType fun zs1 ctorRet1 => do
          let ctorApp1 := mkAppN ctor zs1
          let ctorRet1 ← whnf ctorRet1
          let is1 : Array Expr := ctorRet1.getAppArgs[info.numParams:]
          let ism1 := is1.push ctorApp1
          forallTelescope ctorType fun zs2 ctorRet2 => do
            let ctorApp2 := mkAppN ctor zs2
            let ctorRet2 ← whnf ctorRet2
            let is2 : Array Expr := ctorRet2.getAppArgs[info.numParams:]
            let ism2 := is2.push ctorApp2
            let e := mkAppN motive (ism1 ++ ism2)
            let e ← mkForallFVars (zs1 ++ zs2) e
            let name := match ctorName with
              | Name.str _ s => Name.mkSimple s
              | _ => Name.mkSimple s!"alt{i+1}"
            return (name, e)
      withLocalDeclsDND altTypes fun alts => do

      let ctorApp1 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ ism1)
      let ctorApp2 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ ism2)
      let heqType ← mkEq ctorApp1 ctorApp2
      let heqType' ← mkEq ctorApp2 ctorApp1
      withLocalDeclD `h heqType fun heq => do
        let motive1 ← mkLambdaFVars ism1 (← mkArrow heqType' (mkAppN motive (ism1 ++ ism2)))
        let e := mkConst casesOnInfo.name (v :: us)
        let e := mkAppN e params
        let e := mkApp e motive1
        let e := mkAppN e ism1
        let alts1 ← info.ctors.toArray.mapIdxM fun i ctorName => do
          let ctor := mkAppN (mkConst ctorName us) params
          let ctorType ← inferType ctor
          forallTelescope ctorType fun zs1 ctorRet1 => do
            let ctorApp1 := mkAppN ctor zs1
            let ctorRet1 ← whnf ctorRet1
            let is1 : Array Expr := ctorRet1.getAppArgs[info.numParams:]
            let ism1 := is1.push ctorApp1
            -- Here we let the typecheker reduce the `ctorIdx` application
            let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) ctorApp2 (mkRawNatLit i)
            withLocalDeclD `h heq fun h => do
              let motive2 ← mkLambdaFVars ism2 (mkAppN motive (ism1 ++ ism2))
              let alt ← forallTelescope ctorType fun zs2 _ => do
                mkLambdaFVars zs2 <| mkAppN alts[i]! (zs1 ++ zs2)
              let e := if info.numCtors = 1 then
                let casesOn := mkConst (mkCasesOnName indName) (v :: us)
                mkAppN casesOn (params ++ #[motive2] ++ ism2 ++ #[alt])
              else
                let casesOn := mkConst (mkConstructorElimName indName ctorName) (v :: us)
                mkAppN casesOn (params ++ #[motive2] ++ ism2 ++ #[h, alt])
              mkLambdaFVars (zs1.push h) e
        let e := mkAppN e alts1
        let e := mkApp e (← mkEqSymm heq)
        mkLambdaFVars (params ++ #[motive] ++ ism1 ++ ism2 ++ #[heq] ++ alts) e

  withExporting (isExporting := !isPrivateName declName) do
    addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
      (name        := declName)
      (levelParams := casesOnInfo.levelParams)
      (type        := (← inferType e))
      (value       := e)
      (hints       := ReducibilityHints.abbrev)
    ))
  modifyEnv fun env => markAuxRecursor env declName
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  Elab.Term.elabAsElim.setTag declName
  setReducibleAttribute declName

/--
This constructs a matcher for a match statement that matches on the constructors of
a data type in parallel. So if `h : x1.ctorIdx = x2.ctorIdx`, then it implements
```
match x1, x2, h with
| ctor1 .. , ctor1 .. , _ => ...
| ctor2 .. , ctor2 .. , _ => ...
```
The normal matcher supports such matches, but implements them using nested `casesOn`, which
leads to a quadratic blow-up. This function uses the per-constructor eliminators to implement this
more efficiently.

This is useful for implementing or deriving functionality like `BEq`, `DecidableEq`, `Ord` and
proving their lawfulness.

One could imagine a future where `match` compilation is smart enough to do that automatically; then
this module can be dropped.

Note that for some data types where the indices determine the constructor (e.g. `Vec`), this leads
to less efficient code than the normal matcher, as this needs to read the constructor tag on both
arguments, whereas the normal matcher produces code that reads just the first argument’s tag, and
then boldly reads the second argument’s fields.
-/
public def mkCasesOnSameCtor (declName : Name) (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!

  let casesOnSameCtorHet := declName ++ `het
  mkCasesOnSameCtorHet casesOnSameCtorHet indName
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  forallBoundedTelescope casesOnInfo.type info.numParams fun params t =>
    let t0 := t.bindingBody! -- ignore motive
    forallBoundedTelescope t0 (some info.numIndices) fun is t =>
    forallBoundedTelescope t (some 1) fun x1 _ =>
    forallBoundedTelescope t (some 1) fun x2 _ => do
      let x1 := x1[0]!
      let x2 := x2[0]!
      let ctorApp1 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ is ++ #[x1])
      let ctorApp2 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ is ++ #[x2])
      let heqType ← mkEq ctorApp1 ctorApp2
      withLocalDeclD `h heqType fun heq => do
      let motiveType ← mkForallFVars (is ++ #[x1,x2,heq]) (mkSort v)
      withLocalDecl `motive .implicit motiveType fun motive => do

      let (altTypes, altInfos) ← Array.unzip <$> info.ctors.toArray.mapIdxM fun i ctorName => do
        let ctor := mkAppN (mkConst ctorName us) params
        withSharedCtorIndices ctor fun zs12 is fields1 fields2 => do
          let ctorApp1 := mkAppN ctor fields1
          let ctorApp2 := mkAppN ctor fields2
          let e := mkAppN motive (is ++ #[ctorApp1, ctorApp2, (← mkEqRefl (mkNatLit i))])
          let e ← mkForallFVars zs12 e
          let e ← if zs12.isEmpty then mkArrow (mkConst ``Unit) e else pure e
          let name := match ctorName with
            | Name.str _ s => Name.mkSimple s
            | _ => Name.mkSimple s!"alt{i+1}"
          let altInfo := { numFields := zs12.size, numOverlaps := 0, hasUnitThunk := zs12.isEmpty : Match.AltParamInfo}
          return ((name, e), altInfo)
      withLocalDeclsDND altTypes fun alts => do
        forallBoundedTelescope t0 (some (info.numIndices + 1)) fun ism1' _ =>
        forallBoundedTelescope t0 (some (info.numIndices + 1)) fun ism2' _ => do
        let (motive', newRefls) ←
          withNewEqs (is.push x1) ism1' fun newEqs1 newRefls1 => do
          withNewEqs (is.push x2) ism2' fun newEqs2 newRefls2 => do
            let motive' := mkAppN motive (is ++ #[x1, x2, heq])
            let motive' ← mkForallFVars (newEqs1 ++ newEqs2) motive'
            let motive' ← mkLambdaFVars (ism1' ++ ism2') motive'
            return (motive', newRefls1 ++ newRefls2)
        let casesOn2 := mkConst casesOnSameCtorHet (v :: us)
        let casesOn2 := mkAppN casesOn2 params
        let casesOn2 := mkApp casesOn2 motive'
        let casesOn2 := mkAppN casesOn2 (is ++ #[x1] ++ is ++ #[x2])
        let casesOn2 := mkApp casesOn2 heq
        let altTypes' ← inferArgumentTypesN info.numCtors casesOn2
        let alts' ← info.ctors.toArray.mapIdxM fun i ctorName => do
          let ctor := mkAppN (mkConst ctorName us) params
          let ctorType ← inferType ctor
          forallTelescope ctorType fun zs1 _ctorRet1 => do
          forallTelescope ctorType fun zs2 _ctorRet2 => do
            let altType ← instantiateForall altTypes'[i]! (zs1 ++ zs2)
            let alt ← mkFreshExprSyntheticOpaqueMVar altType
            let goal := alt.mvarId!
            let some (goal, _) ← Cases.unifyEqs? newRefls.size goal {}
                | throwError "unifyEqns? unexpectedly closed goal"
            let hyp := alts[i]!
            let hyp := if zs1.isEmpty && zs2.isEmpty then mkApp hyp (mkConst ``Unit.unit) else hyp
            let [] ← goal.apply hyp
              | throwError "could not apply {hyp} to close\n{goal}"
            mkLambdaFVars (zs1 ++ zs2) (← instantiateMVars alt)
        let casesOn2 := mkAppN casesOn2 alts'
        let casesOn2 := mkAppN casesOn2 newRefls
        let e ← mkLambdaFVars (params ++ #[motive] ++ is ++ #[x1,x2] ++ #[heq] ++ alts) casesOn2

        let decl := .defnDecl (← mkDefinitionValInferringUnsafe
            (name        := declName)
            (levelParams := casesOnInfo.levelParams)
            (type        := (← inferType e))
            (value       := e)
            (hints       := ReducibilityHints.abbrev)
          )
        let matcherInfo : MatcherInfo := {
          numParams := info.numParams
          numDiscrs := info.numIndices + 3
          altInfos
          uElimPos? := some 0
          discrInfos := #[{}, {}, {}]
          overlaps := {}
        }

        -- Compare attributes with `mkMatcherAuxDefinition`
        withExporting (isExporting := !isPrivateName declName) do
          addDecl decl
        Elab.Term.elabAsElim.setTag declName
        Match.addMatcherInfo declName matcherInfo
        setInlineAttribute declName

        enableRealizationsForConst declName
        compileDecl decl


end Lean
