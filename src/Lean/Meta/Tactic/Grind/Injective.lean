/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.FunInfo
public section
namespace Lean.Meta.Grind

builtin_initialize registerTraceClass `grind.inj
builtin_initialize registerTraceClass `grind.inj.assert
builtin_initialize registerTraceClass `grind.debug.inj

/-- Set of Injective theorems. -/
abbrev InjectiveTheorems := Theorems InjectiveTheorem

/-- A collections of sets of Injective theorems. -/
abbrev InjectiveTheoremsArray := TheoremsArray InjectiveTheorem

private partial def getSymbols (proof : Expr) (hasUniverses : Bool) : MetaM (List HeadIndex) := do
  let type ← inferType proof
  forallTelescope type fun xs type => do
    unless type.isAppOfArity ``Function.Injective 3 do
      throwError "invalid `[grind inj]` theorem, resulting type is not of the form `Function.Injective <fun>`{indentExpr type}"
    if xs.isEmpty && hasUniverses then
      throwError "invalid `[grind inj]` theorem, theorem has universe levels, but no hypotheses{indentExpr type}"
    let f := type.appArg!.eta
    let cs ← collectFnNames f
    if cs.isEmpty then
      throwError "invalid `[grind inj]` theorem, injective function must use at least one constant function symbol{indentExpr f}"
    return cs.toList.map (.const ·)
where
  collectFnNames (f : Expr) : MetaM NameSet := do
    if let .const declName _ := f then
      return { declName }
    else
      Prod.snd <$> (go f |>.run {})

  go (e : Expr) : StateRefT NameSet MetaM Unit := do
    if e.isApp then e.withApp fun f args => do
      if let .const declName _ := f then
        modify (·.insert declName)
      let kinds ← NormalizePattern.getPatternArgKinds f args.size
      for h : i in *...args.size do
        let arg  := args[i]
        let kind := kinds[i]?.getD .relevant
        if kind matches .relevant | .typeFormer then
          go arg

private def symbolsToNames (s : List HeadIndex) : List Name :=
  s.map fun
    | .const n => n
    | _ => Name.anonymous

def mkInjectiveTheorem (declName : Name) : MetaM InjectiveTheorem := do
  let info ← getConstInfo declName
  let proof ← getProofForDecl declName
  let symbols ← getSymbols proof !info.levelParams.isEmpty
  trace[grind.inj] "{declName}: {symbolsToNames symbols}"
  return {
    levelParams := #[]
    origin := .decl declName
    proof, symbols
  }

def Extension.addInjectiveAttr (ext : Extension) (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  ext.add (.inj (← mkInjectiveTheorem declName)) attrKind

end Lean.Meta.Grind
