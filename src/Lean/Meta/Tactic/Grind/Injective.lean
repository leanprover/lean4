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

/-- A theorem marked with `@[grind inj]` -/
structure InjectiveTheorem where
  levelParams  : Array Name
  proof        : Expr
  /-- Contains all symbols used in the term `f` at the theorem's conclusion: `Function.Injective f`. -/
  symbols      : List HeadIndex
  origin       : Origin
  deriving Inhabited

instance : TheoremLike InjectiveTheorem where
  getSymbols thm := thm.symbols
  setSymbols thm symbols := { thm with symbols }
  getOrigin thm := thm.origin
  getProof thm := thm.proof
  getLevelParams thm := thm.levelParams

/-- Set of Injective theorems. -/
abbrev InjectiveTheorems := Theorems InjectiveTheorem

private builtin_initialize injectiveTheoremsExt : SimpleScopedEnvExtension InjectiveTheorem (Theorems InjectiveTheorem) ←
  registerSimpleScopedEnvExtension {
      addEntry := Theorems.insert
      initial  := {}
    }

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

def addInjectiveAttr (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  injectiveTheoremsExt.add (← mkInjectiveTheorem declName) attrKind

def eraseInjectiveAttr (declName : Name) : MetaM Unit := do
  let s := injectiveTheoremsExt.getState (← getEnv)
  let s ← s.eraseDecl declName
  modifyEnv fun env => injectiveTheoremsExt.modifyState env fun _ => s

/-- Returns `true` if `declName` has been tagged as an injective theorem using `[grind]`. -/
def isInjectiveTheorem (declName : Name) : CoreM Bool := do
  return injectiveTheoremsExt.getState (← getEnv) |>.contains (.decl declName)

/-- Returns the injective theorems registered in the environment. -/
def getInjectiveTheorems : CoreM InjectiveTheorems := do
  return injectiveTheoremsExt.getState (← getEnv)

def resetInjectiveTheoremsExt : CoreM Unit := do
  modifyEnv fun env => injectiveTheoremsExt.modifyState env fun _ => {}

end Lean.Meta.Grind
