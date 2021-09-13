/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.DecEq
open Lean.Parser.Term
open Meta

def mkDecEqHeader (ctx : Context) (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ctx `DecidableEq 2 indVal

def mkMatch (ctx : Context) (header : Header) (indVal : InductiveVal) (auxFunName : Name) (argNames : Array Name) : TermElabM Syntax := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkSameCtorRhs : List (Syntax × Syntax × Bool) → TermElabM Syntax
    | [] => ``(isTrue rfl)
    | (a, b, recField) :: todo => withFreshMacroScope do
      let rhs ←
        `(if h : $a = $b then
           by subst h; exact $(← mkSameCtorRhs todo):term
          else
           isFalse (by intro n; injection n; apply h _; assumption))
      if recField then
        -- add local instance for `a = b` using the function being defined `auxFunName`
        `(let inst := $(mkIdent auxFunName) $a $b; $rhs)
      else
        return rhs

  mkAlts : TermElabM (Array Syntax) := do
    let mut alts := #[]
    for ctorName₁ in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName₁
      for ctorName₂ in indVal.ctors do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for i in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        if ctorName₁ == ctorName₂ then
          let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
            let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
            let mut patterns  := patterns
            let mut ctorArgs1 := #[]
            let mut ctorArgs2 := #[]
            -- add `_` for inductive parameters, they are inaccessible
            for i in [:indVal.numParams] do
              ctorArgs1 := ctorArgs1.push (← `(_))
              ctorArgs2 := ctorArgs2.push (← `(_))
            let mut todo := #[]
            for i in [:ctorInfo.numFields] do
              let x := xs[indVal.numParams + i]
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
                todo := todo.push (a, b, recField)
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs1:term*))
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs2:term*))
            let rhs ← mkSameCtorRhs todo.toList
            `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
          alts := alts.push alt
        else if (← compatibleCtors ctorName₁ ctorName₂) then
          patterns := patterns ++ #[(← `($(mkIdent ctorName₁) ..)), (← `($(mkIdent ctorName₂) ..))]
          let rhs ← `(isFalse (by intro h; injection h))
          alts ← alts.push (← `(matchAltExpr| | $[$patterns:term],* => $rhs:term))
    return alts

def mkAuxFunction (ctx : Context) : TermElabM Syntax := do
  let auxFunName ← ctx.auxFunNames[0]
  let indVal     ← ctx.typeInfos[0]
  let header     ← mkDecEqHeader ctx indVal
  let mut body   ← mkMatch ctx header indVal auxFunName header.argNames
  let binders    := header.binders
  let type       ← `(Decidable ($(mkIdent header.targetNames[0]) = $(mkIdent header.targetNames[1])))
  `(private def $(mkIdent auxFunName):ident $binders:explicitBinder* : $type:term := $body:term)

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
    let cmds ← liftTermElabM none <| mkDecEqCmds indVal
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
        mkConst ctors[low]
      else if low + 2 == high then
        mkApp4 cond enumType (mkApp2 (mkConst ``Nat.beq) n (mkRawNatLit low)) (mkConst ctors[low]) (mkConst ctors[low+1])
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
  liftTermElabM none <| mkEnumOfNat declName
  liftTermElabM none <| mkEnumOfNatThm declName
  let ofNatIdent  := mkIdent (Name.mkStr declName "ofNat")
  let auxThmIdent := mkIdent (Name.mkStr declName "ofNat_toCtorIdx")
  let indVal ← getConstInfoInduct declName
  let cmd ← `(
    instance : DecidableEq $(mkIdent declName) :=
      fun x y =>
        if h : x.toCtorIdx = y.toCtorIdx then
          isTrue (by have aux := congrArg $ofNatIdent h; rw [$auxThmIdent:ident, $auxThmIdent:ident] at aux; assumption)
        else
          isFalse fun h => by subst h; contradiction
  )
  elabCommand cmd

def mkDecEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported yet
  else if (← isEnumType declNames[0]) then
    mkDecEqEnum declNames[0]
    return true
  else
    mkDecEq declNames[0]

builtin_initialize
  registerBuiltinDerivingHandler `DecidableEq mkDecEqInstanceHandler
  registerTraceClass `Elab.Deriving.decEq

end Lean.Elab.Deriving.DecEq
