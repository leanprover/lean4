/-!
Tests the `@[trusted_axiom]` attribute and the `linter.untrustedAxioms` linter, which warns when a
declaration transitively depends on an axiom not tagged `@[trusted_axiom]`.
-/

axiom untrustedAx : 1 = 2

@[trusted_axiom] axiom trustedAx : 1 = 1

-- The linter is off by default.
#guard_msgs in
theorem offByDefault : 1 = 2 := untrustedAx

set_option linter.untrustedAxioms true

/-! Axiom declarations themselves are not linted, only their uses. -/

#guard_msgs in
axiom anotherUntrustedAx : 2 = 3

#guard_msgs in
@[trusted_axiom] axiom anotherTrustedAx : 2 = 2

/-! Direct use of an untrusted axiom warns; use of a trusted axiom does not. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
theorem usesUntrusted : 1 = 2 := untrustedAx

#guard_msgs in
theorem usesTrusted : 1 = 1 := trustedAx

/-! Transitive dependencies are reported. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
theorem usesTransitively : 2 = 1 := usesUntrusted.symm

/-! All offending axioms are listed in a single warning. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `anotherUntrustedAx`, `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
theorem usesBoth : 1 = 3 := untrustedAx.trans anotherUntrustedAx

/-! Private declarations are linted as well. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
private theorem privateUses : 1 = 2 := untrustedAx

/-!
Internal auxiliary declarations (e.g. `match` functions) are not linted separately; their axioms
are reported once via the surrounding declaration.
-/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
theorem usesViaMatch : (n : Nat) → 1 = 2
  | 0 => untrustedAx
  | _+1 => untrustedAx

/-!
`sorryAx` is not reported for a declaration containing the `sorry` itself, which already produces
the `warn.sorry` warning.
-/

/--
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem usesSorry : 1 = 2 := sorry

/-! Transitive `sorry`s are not covered by `warn.sorry`, so `sorryAx` is reported for them. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `sorryAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
theorem usesSorryTransitively : 2 = 1 := usesSorry.symm

/-! The synchronous elaboration path warns as well. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
set_option Elab.async false in
theorem usesUntrustedSync : 1 = 2 := untrustedAx

/-! `example`s are linted. -/

/--
warning: declaration depends on axioms that are not tagged `@[trusted_axiom]`: `untrustedAx`

Note: This linter can be disabled with `set_option linter.untrustedAxioms false`
-/
#guard_msgs in
example : 1 = 2 := untrustedAx

/-! Explicitly disabling the linter wins over `linter.all`. -/

set_option linter.all true in
set_option linter.untrustedAxioms false in
#guard_msgs in
theorem explicitOff : 1 = 2 := untrustedAx

/-! The attribute can only be applied to axioms in the current module. -/

def notAnAxiom : Nat := 1

/-- error: Cannot add attribute `@[trusted_axiom]` to non-axiom `notAnAxiom` -/
#guard_msgs in
attribute [trusted_axiom] notAnAxiom

/--
error: Cannot add attribute `[trusted_axiom]` to declaration `propext` because it is in an imported module
-/
#guard_msgs in
attribute [trusted_axiom] propext

/--
error: Invalid attribute scope: Attribute `[trusted_axiom]` must be global, not `local`
-/
#guard_msgs in
attribute [local trusted_axiom] anotherUntrustedAx
