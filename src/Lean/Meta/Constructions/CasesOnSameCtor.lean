/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Meta.CompletionName
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Elab.App

namespace Lean

open Meta

/-
def Vec.casesOnSameCtorHet {α}
    {motive : ∀ {n1}, Vec α n1 → ∀ {n2}, Vec α n2 → Sort u}
    {n1} (x1 : Vec α n1)
    {n2} (x2 : Vec α n2)
    (h : x2.ctorIdx = x1.ctorIdx)
    (nil : motive .nil .nil)
    (cons : ∀ x n1 xs y n2 ys, motive (@Vec.cons _ x n1 xs) (@Vec.cons _ y n2 ys)) :
    motive x1 x2 :=
  x1.casesOn (motive := fun _ x' => x2.ctorIdx = x'.ctorIdx → motive x' x2)
    (nil := fun heq =>
      Vec.nil.elim x2 heq (motive := fun _ x' => motive .nil x')
        (nil := nil)
    )
    (cons := fun a1 n1 xs1 heq =>
      Vec.cons.elim x2 heq (motive := fun _ x' => motive (.cons a1 xs1) x')
        (cons := fun a2 n2 xs2 => cons a1 n1 xs1 a2 n2 xs2)
    )
    h
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
              let e := mkConst (mkConstructorElimName indName ctorName) (v :: us)
              let e := mkAppN e params
              let motive2 ← mkLambdaFVars ism2 (mkAppN motive (ism1 ++ ism2))
              let e := mkApp e motive2
              let e := mkAppN e ism2
              let e := mkApp e h
              let alt ← forallTelescope ctorType fun zs2 _ => do
                mkLambdaFVars zs2 <| mkAppN alts[i]! (zs1 ++ zs2)
              let e := mkApp e alt
              mkLambdaFVars (zs1.push h) e
        let e := mkAppN e alts1
        let e := mkApp e (← mkEqSymm heq)
        mkLambdaFVars (params ++ #[motive] ++ ism1 ++ ism2 ++ #[heq] ++ alts) e

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

/-
def Vec.casesOnSameCtor {α}
    (motive : ∀ {n}, (x1 x2 : Vec α n) → Sort u)
    {n}
    (x1 x2 : Vec α n)
    (h : x2.ctorIdx = x1.ctorIdx)
    (nil : motive .nil .nil)
    (cons : ∀ n x xs y ys, motive (@Vec.cons _ x n xs) (@Vec.cons _ y n ys)) :
    motive x1 x2 :=
   Vec.casesOnSameCtorHet
    (motive := @fun n1 x1' n2 x2' => n1 = n → x1' ≍ x1 → n2 = n → x2' ≍ x2 → motive x1 x2)
    x1 x2 h
    (nil := by unify_eqns 4; exact nil)
    (cons := fun a1 n1 xs1 a2 n2 xs2 => by unify_eqns 4; exact cons ..)
    rfl
    .rfl
    rfl
    .rfl
-/

def withSharedIndices (ctor : Expr) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  let ctorType ← inferType ctor
  forallTelescopeReducing ctorType fun zs ctorRet => do
    let ctor1 := mkAppN ctor zs
    let rec go ctor2 todo acc := do
      match todo with
      | [] => k acc ctor1 ctor2
      | z::todo' =>
        if ctorRet.containsFVar z.fvarId! then
          go (mkApp ctor2 z) todo' acc
        else
          let t ← whnfForall (← inferType ctor2)
          assert! t.isForall
          withLocalDeclD t.bindingName! t.bindingDomain! fun z' => do
            go (mkApp ctor2 z') todo' (acc.push z')
    go ctor zs.toList zs


public def mkCasesOnSameCtor (declName : Name) (indName : Name) (casesOnSameCtorHet : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallBoundedTelescope casesOnInfo.type info.numParams fun params t =>
    let t0 := t.bindingBody! -- ignore motive
    forallBoundedTelescope t0 (some info.numIndices) fun is t =>
    forallBoundedTelescope t (some 1) fun x1 _ =>
    forallBoundedTelescope t (some 1) fun x2 _ => do
      let x1 := x1[0]!
      let x2 := x2[0]!
      let motiveType ← mkForallFVars (is ++ #[x1,x2]) (mkSort v)
      withLocalDecl `motive .implicit motiveType fun motive => do

      let ctorApp1 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ is ++ #[x1])
      let ctorApp2 := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ is ++ #[x2])
      let heqType ← mkEq ctorApp1 ctorApp2
      withLocalDeclD `h heqType fun heq => do

      let altTypes ← info.ctors.toArray.mapIdxM fun i ctorName => do
        let ctor := mkAppN (mkConst ctorName us) params
        withSharedIndices ctor fun zs12 ctorApp1 ctorApp2 => do
          let ctorRet1 ← whnf (← inferType ctorApp1)
          let is : Array Expr := ctorRet1.getAppArgs[info.numParams:]
          let e := mkAppN motive (is ++ #[ctorApp1, ctorApp2])
          let e ← mkForallFVars zs12 e
          let name := match ctorName with
            | Name.str _ s => Name.mkSimple s
            | _ => Name.mkSimple s!"alt{i+1}"
          return (name, e)
      withLocalDeclsDND altTypes fun alts => do
        forallBoundedTelescope t0 (some (info.numIndices + 1)) fun ism1' _ =>
        forallBoundedTelescope t0 (some (info.numIndices + 1)) fun ism2' _ => do
        let (motive', newRefls) ←
          withNewEqs (is.push x1) ism1' fun newEqs1 newRefls1 => do
          withNewEqs (is.push x2) ism2' fun newEqs2 newRefls2 => do
            let motive' := mkAppN motive (is ++ #[x1, x2])
            let motive' ← mkForallFVars (newEqs1 ++ newEqs2) motive'
            let motive' ← mkLambdaFVars (ism1' ++ ism2') motive'
            return (motive', newRefls1 ++ newRefls2)
        let casesOn2 := mkConst casesOnSameCtorHet (v :: us)
        let casesOn2 := mkAppN casesOn2 params
        let casesOn2 := mkApp casesOn2 motive'
        let casesOn2 := mkAppN casesOn2 (is ++ #[x1] ++ is ++ #[x2])
        let casesOn2 := mkApp casesOn2 heq
        let altTypes ← inferArgumentTypesN info.numCtors casesOn2
        let alts' ← info.ctors.toArray.mapIdxM fun i ctorName => do
          let ctor := mkAppN (mkConst ctorName us) params
          let ctorType ← inferType ctor
          forallTelescope ctorType fun zs1 _ctorRet1 => do
          forallTelescope ctorType fun zs2 _ctorRet2 => do
            let altType ← instantiateForall altTypes[i]! (zs1 ++ zs2)
            let alt ← mkFreshExprSyntheticOpaqueMVar altType
            let goal := alt.mvarId!
            -- throwError m!"{goal}"
            let some (goal, _) ← Cases.unifyEqs? newRefls.size goal {}
                | throwError "unifyEqns? unexpectedly closed goal"
            let [] ← goal.apply alts[i]!
              | throwError "could not apply {alts[i]!} to close\n{goal}"
            -- throwError m!"{goal}"
            -- goal.admit
            mkLambdaFVars (zs1 ++ zs2) (← instantiateMVars alt)
        let casesOn2 := mkAppN casesOn2 alts'
        let casesOn2 := mkAppN casesOn2 newRefls
        check casesOn2
        -- check casesOn2
        -- let goals ← goal.applyN casesOn2 (n := alts.size)
        -- throwError m!"{casesOn2}"
        mkLambdaFVars (params ++ #[motive] ++ is ++ #[x1,x2] ++ #[heq] ++ alts) casesOn2

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


end Lean
