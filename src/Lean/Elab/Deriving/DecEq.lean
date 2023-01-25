/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Elab.Deriving.BEq

namespace Lean.Elab.Deriving.DecEq
open Lean.Parser.Term
open Meta

def mkDecEqHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `DecidableEq 0 indVal

def mkMatch (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Term := do
  let discrs := (← mkDiscrs header indVal) ++ #[← `(matchDiscr| lhs), ← `(matchDiscr| rhs)]
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName₁ in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName₁
      for ctorName₂ in indVal.ctors do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        if ctorName₁ == ctorName₂ then
          let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
            let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
            let mut patterns  := patterns
            let mut ctorArgs1 := #[]
            let mut ctorArgs2 := #[]
            -- add `_` for inductive parameters, they are inaccessible
            for _ in [:indVal.numParams] do
              ctorArgs1 := ctorArgs1.push (← `(_))
              ctorArgs2 := ctorArgs2.push (← `(_))
            let mut rhs ← `(Bool.true_iff)
            for i in [:ctorInfo.numFields] do
              let x := xs[indVal.numParams + i]!
              if type.containsFVar x.fvarId! then
                -- If resulting type depends on this field, we don't need to compare
                ctorArgs1 := ctorArgs1.push (← `(_))
                ctorArgs2 := ctorArgs2.push (← `(_))
              else
                let a := mkIdent (← mkFreshUserName `a)
                let b := mkIdent (← mkFreshUserName `b)
                ctorArgs1 := ctorArgs1.push a
                ctorArgs2 := ctorArgs2.push b
                let recField  := (← inferType x).isAppOf indVal.name
                let isProof := (← inferType (← inferType x)).isProp
                if isProof then
                  pure () -- skip
                else if recField then
                  rhs ← `(Bool.and_iff_congr $rhs ($(mkIdent auxFunName) $a $b))
                else
                  rhs ← `(Bool.and_iff_congr $rhs (@beq_iff_eq _ _ $a $b))
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs1:term*))
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs2:term*))
            rhs ← `(by
              refine .trans $rhs ⟨?_, ?_⟩
              · intro h; simp only [h] -- solves True ∧ a=b ∧ c=d → ctor a c = ctor b d
              · intro h; cases h; trivial) -- solves ctor a c = ctor b d → True ∧ a=b ∧ c=d
            `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
          alts := alts.push alt
        else if (← compatibleCtors ctorName₁ ctorName₂) then
          patterns := patterns ++ #[(← `($(mkIdent ctorName₁) ..)), (← `($(mkIdent ctorName₂) ..))]
          let rhs ← `(⟨(nomatch ·), (nomatch ·)⟩)
          alts := alts.push (← `(matchAltExpr| | $[$patterns:term],* => $rhs:term))
    return alts

def mkAuxFunction (ctx : Context) : TermElabM Syntax := do
  let auxFunName := ctx.auxFunNames[0]!
  let indVal     :=ctx.typeInfos[0]!
  let header     ← mkDecEqHeader indVal
  let mut body   ← mkMatch header indVal (← `(ident| deriving_beq_aux)).1.getId
  let binders    := header.binders
  `(theorem deriving_beq_aux $binders:bracketedBinder* (lhs rhs : $(header.targetType)) :
      lhs == rhs ↔ lhs = rhs := $body
    abbrev $(mkIdent auxFunName):ident $binders:bracketedBinder* : DecidableEq $(header.targetType) where
      beq_iff_eq := deriving_beq_aux ..)

def mkDecEqCmds (indVal : InductiveVal) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "decEq" indVal.name
  let cmds := #[← mkAuxFunction ctx] ++ (← mkInstanceCmds ctx `DecidableEq #[indVal.name] (useAnonCtor := false))
  trace[Elab.Deriving.decEq] "\n{cmds}"
  return cmds

open Command

def mkDecEq (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  if indVal.isNested then
    return false -- nested inductive types are not supported yet
  else
    let cmds ← liftTermElabM <| mkDecEqCmds indVal
    cmds.forM elabCommand
    return true

partial def mkEnumOfNat (declName : Name) : MetaM Unit := do
  let indVal ← getConstInfoInduct declName
  let enumType := mkConst declName
  let ctors := indVal.ctors.toArray
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let cond := mkConst ``cond [levelZero]
    let rec mkDecTree (low high : Nat) : Expr :=
      if low + 1 == high then
        mkConst ctors[low]!
      else if low + 2 == high then
        mkApp4 cond enumType (mkApp2 (mkConst ``Nat.beq) n (mkRawNatLit low)) (mkConst ctors[low]!) (mkConst ctors[low+1]!)
      else
        let mid := (low + high)/2
        let lowBranch := mkDecTree low mid
        let highBranch := mkDecTree mid high
        mkApp4 cond enumType (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit mid) n) highBranch lowBranch
    let value ← mkLambdaFVars #[n] (mkDecTree 0 ctors.size)
    let type ← mkArrow (mkConst ``Nat) enumType
    addAndCompile <| Declaration.defnDecl {
      name := Name.mkStr declName "ofNat"
      levelParams := []
      safety := DefinitionSafety.safe
      hints  := ReducibilityHints.abbrev
      value, type
    }

def mkEnumOfNatThm (declName : Name) : MetaM Unit := do
  let indVal ← getConstInfoInduct declName
  let toCtorIdx := mkConst (Name.mkStr declName "toCtorIdx")
  let ofNat     := mkConst (Name.mkStr declName "ofNat")
  let enumType  := mkConst declName
  let eqEnum    := mkApp (mkConst ``Eq [levelOne]) enumType
  let rflEnum   := mkApp (mkConst ``Eq.refl [levelOne]) enumType
  let ctors := indVal.ctors
  withLocalDeclD `x enumType fun x => do
    let resultType := mkApp2 eqEnum (mkApp ofNat (mkApp toCtorIdx x)) x
    let motive     ← mkLambdaFVars #[x] resultType
    let casesOn    := mkConst (mkCasesOnName declName) [levelZero]
    let mut value  := mkApp2 casesOn motive x
    for ctor in ctors do
      value := mkApp value (mkApp rflEnum (mkConst ctor))
    value ← mkLambdaFVars #[x] value
    let type ← mkForallFVars #[x] resultType
    addAndCompile <| Declaration.thmDecl {
      name := Name.mkStr declName "ofNat_toCtorIdx"
      levelParams := []
      value, type
    }

def mkDecEqEnum (declName : Name) : CommandElabM Unit := do
  liftTermElabM <| mkEnumOfNat declName
  liftTermElabM <| mkEnumOfNatThm declName
  let ofNatIdent  := mkIdent (Name.mkStr declName "ofNat")
  let auxThmIdent := mkIdent (Name.mkStr declName "ofNat_toCtorIdx")
  let cmd ← `(
    instance : DecidableEq $(mkIdent declName) :=
      .ofInj (·.toCtorIdx) @fun x y h => by
        -- We use `rfl` in the following proof because the first script fails for unit-like datatypes due to etaStruct.
        first | have aux := congrArg $ofNatIdent h; rw [$auxThmIdent:ident, $auxThmIdent:ident] at aux; assumption | rfl)
  trace[Elab.Deriving.decEq] "\n{cmd}"
  elabCommand cmd

def mkDecEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  -- Call BEq derive handler first, as we require the automatically derived BEq instance.
  _ ← BEq.mkBEqInstanceHandler declNames
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported yet
  else if (← isEnumType declNames[0]!) then
    mkDecEqEnum declNames[0]!
    return true
  else
    mkDecEq declNames[0]!

builtin_initialize
  registerDerivingHandler `DecidableEq mkDecEqInstanceHandler
  registerTraceClass `Elab.Deriving.decEq

end Lean.Elab.Deriving.DecEq
