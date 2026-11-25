module

/-!
Tests for `linter.checkRespectTransparency` and its sub-options. The sub-option
`linter.checkRespectTransparency.instances` warns when the elaborator accepts a value whose expected
type is a class, or a function type with a class codomain, although its type agrees with the expected
type only above `.instances` transparency, and instance synthesis finds no instance of the expected
type that is defeq to the value. The linter does not change the elaborated term. Instance families
are compared like in `isDefEq`: binder types at `.implicit`, codomains at `.instances`.
-/

/-- A plain type synonym: `MyNat` unfolds at `.default`, not at `.instances` or `.implicit`. -/
def MyNat := Nat

def addWith (α : Type) (inst : Add α) (a b : α) : α := inst.add a b
def addWithImplicit {α : Type} {inst : Add α} (a b : α) : α := inst.add a b

/-! The linter is off by default. -/

#guard_msgs in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b

/-! The parent option `linter.checkRespectTransparency` enables the sub-option. -/

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
set_option linter.checkRespectTransparency true in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b

set_option linter.checkRespectTransparency.instances true

/-! An explicit instance argument of the other spelling, without an instance for `MyNat`. -/

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b

/-! The same for an implicit argument given by name, a type ascription and an instance declaration. -/

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
example (a b : MyNat) : MyNat := addWithImplicit (inst := instAddNat) a b

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
example : Add MyNat := (instAddNat : Add MyNat)

def MyNat4 := Nat

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat4
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
instance : Add MyNat4 := instAddNat

/-! Postponed values: the types are compared even though the value is still a metavariable. -/

/--
warning: The value that Lean elaborates later (for example a tactic block)
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
example [Add Nat] : Add MyNat := ‹Add Nat›

/-!
No synthesis fallback: an instance for `MyNat2` that is defeq to `instAddNat` exists, but the term
still contains `instAddNat` at a position for `Add MyNat2`, so the linter warns.
-/

def MyNat2 := Nat
instance : Add MyNat2 := ⟨Nat.add⟩

/--
warning: The value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat2
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency.

Note: This linter can be disabled with `set_option linter.checkRespectTransparency.instances false`
-/
#guard_msgs in
example (a b : MyNat2) : MyNat2 := addWith MyNat2 instAddNat a b

/-! Exempt: propositional classes. -/

class IsGood (α : Type) : Prop where
instance : IsGood Nat := ⟨⟩
def needGood (α : Type) (_ : IsGood α) : Nat := 0

#guard_msgs in
example : Nat := needGood MyNat (inferInstanceAs (IsGood Nat))

/-! Instance families: binder types need to agree only at `.implicit`. -/

@[implicit_reducible] def two := 2
class C (n : Nat) where
instance (n : Nat) : C n := ⟨⟩
def famWith (n : Nat) (_ : ∀ _ : Fin n, C 3) : Nat := n

#guard_msgs in
example (h : ∀ _ : Fin 2, C 3) : Nat := famWith two h

/-! The parent option enables the sub-option; setting the sub-option overrides it. -/

set_option linter.checkRespectTransparency.instances false in
#guard_msgs in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b
