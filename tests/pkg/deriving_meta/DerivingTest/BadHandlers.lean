module

public meta import Lean.Elab.Deriving.Meta

public meta section

open Lean Meta Elab Command Deriving

/-!
# Examples of bad deriving handlers

Here we define deriving handlers that are not implemented correctly or don't work because of
current limitations, to test error messages.

We run them directly here instead of using the `deriving` syntax because then the tests would need
to live in a different files than the handlers.
-/

/-!
If some fields are unhandled in `makeInstancesUsingCtor` (and we have a`| _ => .unhandled`
alternative), we generate an error message.
-/

class Multi (α : Type u) where
  one : Name
  other : Name

meta def deriveMulti : DerivingHandler :=
  mkInductiveDerivingHandler ``Multi do
    makeInstancesUsingCtor fun
      | ``Multi.one => fun input => return .inline <| toExpr input.induct
      | _ => .unhandled
    return true

/--
error: Internal error in deriving handler for `Multi`:
Unhandled field `Multi.other`
-/
#guard_msgs in
run_cmd deriveMulti #[``Bool]

/-!
We don't allow dependencies for `.doubleCases` and `.doubleCasesSlow`
-/

class DecEqLike (α : Type u) where
  decEq : (a b : α) → Decidable (a = b)

meta def deriveDecEqLike : DerivingHandler :=
  mkInductiveDerivingHandler ``DecEqLike do
    makeInstancesUsingCtor fun
      | ``DecEqLike.decEq => .doubleCases (fun _ => unreachable!) (fun _ => unreachable!)
      | _ => .unhandled
    return true

/--
error: Invalid use of `FieldHelperProvider.doubleCases`, the target type for `DecEqLike.decEq`
depends on the type parameter or the field arguments
-/
#guard_msgs in
run_cmd deriveDecEqLike #[``Bool]

class Merge (α : Type u) where
  merge : α → α → α

meta def deriveMerge : DerivingHandler :=
  mkInductiveDerivingHandler ``Merge do
    makeInstancesUsingCtor fun
      | ``Merge.merge => .doubleCases (fun _ => unreachable!) (fun _ => unreachable!)
      | _ => .unhandled
    return true

/--
error: Invalid use of `FieldHelperProvider.doubleCases`, the target type for `Merge.merge`
depends on the type parameter or the field arguments
-/
#guard_msgs in
run_cmd deriveMerge #[``List]

/-!
Inside of `@[expose] public section`s or with `deriving @[expose]`, instances are type-checked in
the public scope before being added, catching public deriving handlers using private things
-/

class Summary (α : Type u) where
  typeName : String
  size : α → Nat

private def secretName : String := "secret"

meta def summaryHandler (nameDecl : MetaM Name) : DerivingHandler :=
  mkInductiveDerivingHandler ``Summary do
    makeInstancesUsingCtor fun
      | ``Summary.typeName =>
        fun _ => return .inline (mkConst (← nameDecl))
      | ``Summary.size =>
        .cases fun _ _ _ _ _ => return mkNatLit 1
      | _ => .unhandled
    return true

meta def secretHandler : DerivingHandler :=
  summaryHandler do return mkPrivateName (← getEnv) `secretName

@[expose] public section

/--
error: Instance `instSummaryBool` failed to type check
  Unknown constant `_private.DerivingTest.BadHandlers.0.secretName`
  ⏎
  Note: A private declaration `secretName` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
run_cmd secretHandler #[``Bool]

end
