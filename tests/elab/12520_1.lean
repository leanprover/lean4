import Lean


structure T where
  val : Bool
  proof : True

variable (x : True → T)

example : (T.mk (x True.intro).val) = (fun h => x h) := rfl
example : (fun h => x h) = x := rfl
example : (T.mk (x True.intro).val) = x := rfl

open Lean Meta

structure EtaAdmissionBox where
  val : Bool

@[reducible] def EtaAdmissionAlias := Bool → EtaAdmissionBox

private def explicitType : Expr :=
  .forallE `_ (mkConst ``Bool) (mkConst ``EtaAdmissionBox) .default

private def aliasType : Expr :=
  .const ``EtaAdmissionAlias []

private def theoremType (domain : Expr) : Expr :=
  .forallE `f domain
    (mkApp3 (mkConst ``Eq [1]) domain (.bvar 0)
      (.const ``EtaAdmissionBox.mk []))
    .default

private def theoremValue (domain : Expr) : Expr :=
  .lam `f domain
    (mkApp2 (mkConst ``Eq.refl [1]) domain (.bvar 0))
    .default

private def expectDeclTypeMismatch
    (env : Environment) (name : Name) (domain : Expr) : MetaM Unit := do
  let type := theoremType domain
  let value := theoremValue domain
  assert! !type.hasFVar && !type.hasMVar && !type.hasLooseBVars
  assert! !value.hasFVar && !value.hasMVar && !value.hasLooseBVars
  let decl : Declaration := .thmDecl {
    name := name
    levelParams := []
    type := type
    value := value
  }
  let inferredType ← inferType value
  let passedElab ← isDefEq type inferredType
  if passedElab then
    throwError m!"BUG: elaborator accepted invalid declaration {name}"
  match env.addDeclCore 0 0 decl none (doCheck := true) with
  | .ok _ =>
      throwError m!"BUG: checked admission accepted invalid declaration {name}"
  | .error (.declTypeMismatch ..) =>
      pure ()
  | .error e =>
      throwError m!"unexpected kernel exception for {name}: {e.toMessageData {}}"

run_meta do
  let env ← getEnv
  expectDeclTypeMismatch env `etaAliasMustReject aliasType
  expectDeclTypeMismatch env `etaExplicitMustReject explicitType
