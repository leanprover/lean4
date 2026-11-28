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

meta def deriveSummary (nameDecl : MetaM Name) : DerivingHandler :=
  mkInductiveDerivingHandler ``Summary do
    makeInstancesUsingCtor fun
      | ``Summary.typeName =>
        fun _ => return .inline (mkConst (← nameDecl))
      | ``Summary.size =>
        .cases fun _ _ _ _ _ => return mkNatLit 1
      | _ => .unhandled
    return true

meta def secretHandler : DerivingHandler :=
  deriveSummary do return mkPrivateName (← getEnv) `secretName

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

/-!
You can only use recursion if you use the instance projection functions, wrappers don't work
-/

class BadRec (α : Type u) where
  parity : α → Bool

abbrev parity := @BadRec.parity

meta def deriveBadRec : DerivingHandler :=
  mkInductiveDerivingHandler ``BadRec do
    deriveTransformationInstPerConstructor fun _ival cval fields _ctorApp => do
      let mut parity := toExpr (cval.cidx % 2 == 1)
      for field in fields do
        if ← isProof field then
          continue
        let type ← inferType field
        let some lvl ← getDecLevel? type
          | throwError "Field type `{type}` has an unexpected level `{← getLevel field}`"
        let inst ← synthInstanceDeriving (.app (.const ``BadRec [lvl]) type)
        let b := mkApp3 (.const ``parity [lvl]) type inst field
        parity := mkApp2 (.const ``Bool.xor []) parity b
      return parity

instance : BadRec Nat where
  parity n := n % 2 == 1

-- works for non-recursive inductives
run_cmd deriveBadRec #[``Fin]

-- but not for recursive ones
/--
error: fail to show termination for
  instBadRecList.parity
with errors
failed to infer structural recursion:
Not considering parameter α of instBadRecList.parity:
  it is unchanged in the recursive calls
Not considering parameter #2 of instBadRecList.parity:
  it is unchanged in the recursive calls
Cannot use parameter t:
  insufficient number of parameters at recursive application ⏎
    instBadRecList.parity α


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u
head : α
tail a✝ : List α
⊢ sizeOf a✝ < 1 + sizeOf tail
-/
#guard_msgs in
run_cmd deriveBadRec #[``List]
