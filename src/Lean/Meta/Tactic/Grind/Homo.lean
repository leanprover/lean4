/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.AppBuilder
public section
namespace Lean.Meta.Grind

/-- Extension backing the `@[grind homo]` attribute. -/
builtin_initialize homoExt : Sym.Simp.SymSimpExtension ← Sym.Simp.mkSymSimpExt

/-- Returns the homomorphism rules tagged with the `[grind homo]` attribute. -/
def getHomoTheorems : CoreM Sym.Simp.Theorems :=
  homoExt.getTheorems

/-- A theorem tagged with the `[grind homo_pred]` attribute. -/
structure HomoPredTheorem where
  /-- Name of the theorem. -/
  declName : Name
  /-- Number of explicit parameters. The theorem is instantiated with the trailing
  `arity` arguments of the triggering application. -/
  arity : Nat
  deriving Inhabited, BEq

/-- Map from trigger head symbol to the `[grind homo_pred]` theorems it activates. -/
abbrev HomoPredTheorems := NameMap (List HomoPredTheorem)

/-- Extension backing the `@[grind homo_pred]` attribute. -/
builtin_initialize homoPredExt : SimpleScopedEnvExtension (Name × HomoPredTheorem) HomoPredTheorems ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun s (key, thm) => s.insert key (thm :: (s.find? key).getD [])
  }

/-- Returns the homomorphism predicates tagged with the `[grind homo_pred]` attribute. -/
def getHomoPredTheorems : CoreM HomoPredTheorems :=
  return homoPredExt.getState (← getEnv)

/--
Validates and registers a `[grind homo_pred]` theorem.
The conclusion of the theorem must contain an application whose trailing arguments are
exactly the theorem's explicit parameters. The head symbol of this application is the
trigger for the theorem.
-/
def addHomoPredAttr (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo declName
  unless (← isProp info.type) do
    throwError "invalid `[grind homo_pred]` theorem, `{.ofConstName declName}` is not a proposition"
  forallTelescope info.type fun xs type => do
    let xsExplicit ← xs.filterM fun x => return (← getFVarLocalDecl x).binderInfo.isExplicit
    let found? := type.find? fun e => Id.run do
      unless e.isApp && e.getAppFn.isConst do return false
      let args := e.getAppArgs
      if args.size < xsExplicit.size then return false
      return args.extract (args.size - xsExplicit.size) args.size == xsExplicit
    let some found := found?
      | throwError "invalid `[grind homo_pred]` theorem, the conclusion of `{.ofConstName declName}` does not contain an application whose trailing arguments are the theorem's explicit parameters"
    let .const key _ := found.getAppFn | unreachable!
    homoPredExt.add (key, { declName, arity := xsExplicit.size }) attrKind

/--
Returns the instances of the `[grind homo_pred]` theorems triggered by `e`.
Each instance is a pair `(proof, prop)` where `proof : prop`. A registered theorem
whose trigger matches `e`'s head symbol is instantiated with `e`'s trailing arguments;
instantiations that fail to elaborate (e.g. because the argument types do not match)
are discarded.
-/
def mkHomoPredInstances (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let .const declName _ := e.getAppFn | return #[]
  let some thms := (← getHomoPredTheorems).find? declName | return #[]
  let args := e.getAppArgs
  let mut result := #[]
  for thm in thms do
    if args.size ≥ thm.arity then
      try
        let proof ← mkAppM thm.declName (args.extract (args.size - thm.arity) args.size)
        result := result.push (proof, ← inferType proof)
      catch _ =>
        pure ()
  return result

end Lean.Meta.Grind
