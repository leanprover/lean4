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

def mkDecEqHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `DecidableEq 2 indVal

def mkMatch (ctx : Context) (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkSameCtorRhs : List (Ident × Ident × Option Name × Bool) → TermElabM Term
    | [] => ``(isTrue rfl)
    | (a, b, recField, isProof) :: todo => withFreshMacroScope do
      let rhs ← if isProof then
        `(have h : @$a = @$b := rfl; by subst h; exact $(← mkSameCtorRhs todo):term)
      else
        `(if h : @$a = @$b then
           by subst h; exact $(← mkSameCtorRhs todo):term
          else
           isFalse (by intro n; injection n; apply h _; assumption))
      if let some auxFunName := recField then
        -- add local instance for `a = b` using the function being defined `auxFunName`
        `(let inst := $(mkIdent auxFunName) @$a @$b; $rhs)
      else
        return rhs

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
            let mut todo := #[]
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
                let indValNum :=
                  ctx.typeInfos.findIdx?
                  ((← inferType x).isAppOf ∘ ConstantVal.name ∘ InductiveVal.toConstantVal)
                let recField  := indValNum.map (ctx.auxFunNames[·]!)
                let isProof   := (← inferType (← inferType x)).isProp
                todo := todo.push (a, b, recField, isProof)
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs1:term*))
            patterns := patterns.push (← `(@$(mkIdent ctorName₁):ident $ctorArgs2:term*))
            let rhs ← mkSameCtorRhs todo.toList
            `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
          alts := alts.push alt
        else if (← compatibleCtors ctorName₁ ctorName₂) then
          patterns := patterns ++ #[(← `($(mkIdent ctorName₁) ..)), (← `($(mkIdent ctorName₂) ..))]
          let rhs ← `(isFalse (by intro h; injection h))
          alts := alts.push (← `(matchAltExpr| | $[$patterns:term],* => $rhs:term))
    return alts

def mkAuxFunction (ctx : Context) (auxFunName : Name) (indVal : InductiveVal): TermElabM (TSyntax `command) := do
  let header  ← mkDecEqHeader indVal
  let body    ← mkMatch ctx header indVal
  let binders := header.binders
  let type    ← `(Decidable ($(mkIdent header.targetNames[0]!) = $(mkIdent header.targetNames[1]!)))
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $type:term := $body:term)

def mkAuxFunctions (ctx : Context) : TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:ctx.auxFunNames.size] do
    let auxFunName := ctx.auxFunNames[i]!
    let indVal     := ctx.typeInfos[i]!
    res := res.push (← mkAuxFunction ctx auxFunName indVal)
  `(command| mutual $[$res:command]* end)

def mkDecEqCmds (indVal : InductiveVal) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "decEq" indVal.name
  let cmds := #[← mkAuxFunctions ctx] ++ (← mkInstanceCmds ctx `DecidableEq #[indVal.name] (useAnonCtor := false))
  trace[Elab.Deriving.decEq] "\n{cmds}"
  return cmds

open Command

def mkDecEq (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  if indVal.isNested then
    return false -- nested inductive types are not supported yet
  else
    let cmds ← liftTermElabM <| mkDecEqCmds indVal
    -- `cmds` can have a number of syntax nodes quadratic in the number of constructors
    -- and thus create as many info tree nodes, which we never make use of but which can
    -- significantly slow down e.g. the unused variables linter; avoid creating them
    withEnableInfoTree false do
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
      fun x y =>
        if h : x.toCtorIdx = y.toCtorIdx then
          -- We use `rfl` in the following proof because the first script fails for unit-like datatypes due to etaStruct.
          isTrue (by first | have aux := congrArg $ofNatIdent h; rw [$auxThmIdent:ident, $auxThmIdent:ident] at aux; assumption | rfl)
        else
          isFalse fun h => by subst h; contradiction
  )
  trace[Elab.Deriving.decEq] "\n{cmd}"
  elabCommand cmd

def mkDecEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← isEnumType declNames[0]!) then
    mkDecEqEnum declNames[0]!
    return true
  else
    mkDecEq declNames[0]!

builtin_initialize
  registerDerivingHandler `DecidableEq mkDecEqInstanceHandler
  registerTraceClass `Elab.Deriving.decEq

end Lean.Elab.Deriving.DecEq
