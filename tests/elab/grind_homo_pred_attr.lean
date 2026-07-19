import Lean

/-!
Tests for `[grind homo_pred]` attribute registration. Homomorphism predicates are
registered in an environment extension mapping the trigger head symbol to the tagged
theorems, retrievable via `Lean.Meta.Grind.getHomoPredTheorems`. The registered
theorems can be instantiated for concrete terms via
`Lean.Meta.Grind.mkHomoPredInstances`.
-/

open Lean Meta Grind

structure W where
  val : Int

instance : Add W := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : LE W := ⟨fun a b => a.val ≤ b.val⟩

def wu (x : W) : Int := x.val

axiom wu_lower (x : W) : 0 ≤ wu x
axiom wu_upper (x : W) : wu x < 2^32
axiom le_iff (a b : W) : a ≤ b ↔ wu a ≤ wu b

attribute [grind homo_pred] wu_lower
attribute [grind homo_pred] wu_upper
attribute [grind homo_pred] le_iff

/--
Displays the `[grind homo_pred]` entries registered by this file. The extension also
contains the predicates from `Init.Grind.Homo`, so we only display the theorems
declared at the root namespace (i.e. the ones in this file).
-/
def showPredMap : MetaM Unit := do
  let map ← getHomoPredTheorems
  for (key, thms) in map do
    for thm in thms do
      if thm.declName.getPrefix.isAnonymous then
        logInfo m!"{key} -> {thm.declName} (arity {thm.arity})"

/--
info: LE.le -> le_iff (arity 2)
---
info: wu -> wu_upper (arity 1)
---
info: wu -> wu_lower (arity 1)
-/
#guard_msgs in
run_meta showPredMap

/--
Instantiates the registered predicates for `wu (x + y)`, `x ≤ y` (over `W`), and
`(0 : Int) ≤ 0`. The last one triggers `le_iff`, but the instantiation fails because
the arguments are not of type `W`, so no fact is produced for it.
-/
def checkInstances : MetaM Unit := do
  withLocalDeclD `x (mkConst ``W) fun x => do
  withLocalDeclD `y (mkConst ``W) fun y => do
    let e ← mkAppM ``wu #[← mkAppM ``HAdd.hAdd #[x, y]]
    for (proof, prop) in ← mkHomoPredInstances e do
      Meta.check proof
      logInfo m!"{prop}"
    let e ← mkAppM ``LE.le #[x, y]
    for (proof, prop) in ← mkHomoPredInstances e do
      Meta.check proof
      logInfo m!"{prop}"
    let e ← mkAppM ``LE.le #[toExpr (0 : Int), toExpr (0 : Int)]
    for (_, prop) in ← mkHomoPredInstances e do
      logInfo m!"unexpected: {prop}"

/--
info: wu (x + y) < 2 ^ 32
---
info: 0 ≤ wu (x + y)
---
info: x ≤ y ↔ wu x ≤ wu y
-/
#guard_msgs in
run_meta checkInstances

/-! Error conditions. -/

/-- error: invalid `[grind homo_pred]` theorem, `wu` is not a proposition -/
#guard_msgs in
attribute [grind homo_pred] wu

axiom not_covering (x : W) (n : Nat) : 0 ≤ wu x

/--
error: invalid `[grind homo_pred]` theorem, the conclusion of `not_covering` does not contain an application whose trailing arguments are the theorem's explicit parameters
-/
#guard_msgs in
attribute [grind homo_pred] not_covering

axiom all_implicit {a b : W} : a ≤ b ↔ wu a ≤ wu b

/--
error: invalid `[grind homo_pred]` theorem, `all_implicit` must have at least one explicit parameter; the trigger is inferred from an application whose trailing arguments are the theorem's explicit parameters
-/
#guard_msgs in
attribute [grind homo_pred] all_implicit

/-- error: homomorphism predicates must be set using the default `[grind]` attribute -/
#guard_msgs in
attribute [lia homo_pred] wu_lower

/--
error: homomorphism predicates should be registered using the `@[grind homo_pred]` attribute
-/
#guard_msgs in
example : True := by grind [homo_pred wu_lower]

/-! `reset_grind_attrs%` clears the homo_pred extension. -/

reset_grind_attrs%

#guard_msgs in
run_meta showPredMap
