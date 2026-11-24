module

/-!
Tests for `backward.elab.instanceTypes`: a value whose expected type is a class, or a function type
with a class codomain, must have that type at `.instances` transparency, whatever its binder kind.
If it does not, the elaborator synthesizes an instance of the expected type and accepts the value
only if it is defeq to that instance. Instance families are compared like in `isDefEq`: binder
types at `.implicit`, codomains at `.instances`.
-/

set_option backward.elab.instanceTypes true

/-- A plain type synonym: `MyNat` unfolds at `.default`, not at `.instances` or `.implicit`. -/
def MyNat := Nat

def addWith (α : Type) (inst : Add α) (a b : α) : α := inst.add a b
def addWithImplicit {α : Type} {inst : Add α} (a b : α) : α := inst.add a b

/-! An explicit instance argument of the other spelling, without an instance for `MyNat`. -/

/--
error: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b

/-! The same for an implicit argument given by name, and for a type ascription. -/

/--
error: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example (a b : MyNat) : MyNat := addWithImplicit (inst := instAddNat) a b

/--
error: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example : Add MyNat := (instAddNat : Add MyNat)

/-! The opt-out. -/

set_option backward.elab.instanceTypes false in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b

/-!
Synthesis fallback: with an instance for `MyNat2` that is defeq to `instAddNat`, the value is
accepted. The instance itself must be stated at the type `Add MyNat2`.
-/

def MyNat2 := Nat
instance : Add MyNat2 := ⟨Nat.add⟩

example (a b : MyNat2) : MyNat2 := addWith MyNat2 instAddNat a b

/-! The fallback does not accept an instance that differs from the synthesized one. -/

def MyNat3 := Nat
instance : Add MyNat3 := ⟨fun a _ => a⟩

/-! An instance declaration whose value has the other spelling is rejected, too. -/

def MyNat4 := Nat

/--
error: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat4
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
instance : Add MyNat4 := instAddNat

/--
error: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat3
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example (a b : MyNat3) : MyNat3 := addWith MyNat3 instAddNat a b

/-! Exempt: propositional classes and classes marked `@[lax_instance_defeq]`. -/

class IsGood (α : Type) : Prop where
instance : IsGood Nat := ⟨⟩
def needGood (α : Type) (_ : IsGood α) : Nat := 0

example : Nat := needGood MyNat (inferInstanceAs (IsGood Nat))

set_option linter.deprecated.laxInstanceDefeq false in
@[lax_instance_defeq] class LaxC (α : Type) where
instance : LaxC Nat := ⟨⟩
def needLax (α : Type) (_ : LaxC α) : Nat := 0

example : Nat := needLax MyNat (inferInstanceAs (LaxC Nat))

/-!
Instance families: the binder types only need to agree at `.implicit`, the codomains at
`.instances`. `two` is `implicit_reducible`, so `Fin two` and `Fin 2` agree at `.implicit` but not
at `.instances`.
-/

@[implicit_reducible] def two := 2

class C (n : Nat) where
instance (n : Nat) : C n := ⟨⟩

def famWith (n : Nat) (_ : ∀ _ : Fin n, C 3) : Nat := n

example : Nat := famWith two (fun _ : Fin 2 => inferInstance)

/-!
A codomain of the other spelling is still rejected. The elaborator reports it at the body of the
family, which it elaborates against the codomain `D three`.
-/

def three := 3
class D (n : Nat) where
instance : D 3 := ⟨⟩
def famWith' (n : Nat) (_ : ∀ _ : Fin n, D three) : Nat := n

/--
error: Type mismatch at `.instances` transparency: the value
  inferInstance
has type
  D 3
but is expected to have type
  D three
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example : Nat := famWith' two (fun _ : Fin 2 => (inferInstance : D 3))

/-! The same for families given as a hypothesis instead of a lambda. -/

example (h : ∀ _ : Fin 2, C 3) : Nat := famWith two h

/--
error: Type mismatch at `.instances` transparency: the value
  h
has type
  Fin 2 → D 3
but is expected to have type
  Fin two → D three
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
example (h : ∀ _ : Fin 2, D 3) : Nat := famWith' two h

/-! `debug.elab.instanceTypes.asWarning` reports the failure as a warning and accepts the value. -/

/--
warning: Type mismatch at `.instances` transparency: the value
  instAddNat
has type
  Add Nat
but is expected to have type
  Add MyNat
The two types agree only when Lean unfolds definitions that are not reducible at `.instances` transparency, and instance synthesis found no instance of the expected type that is defeq to the value.

Note: Disable this check with `set_option backward.elab.instanceTypes false`.
-/
#guard_msgs in
set_option debug.elab.instanceTypes.asWarning true in
example (a b : MyNat) : MyNat := addWith MyNat instAddNat a b
