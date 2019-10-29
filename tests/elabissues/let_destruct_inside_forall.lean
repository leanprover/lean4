axiom Foo : Type
axiom foo : Foo

/- This works -/
def works : Prop :=
-- ∀ (x : Foo),
let ⟨foo₁, foo₂⟩ := (foo, foo);
false

/-
The following tests fail because the elaborator fails to propagate the expected type. The main issue is that the elaborator is missing the following case:

If the expected type is `Prop` for an expression `Forall (x : A), t`, then we should also elaborate `t` with expected type `Prop`. Note that every single example works if we write them as `Forall (x : A), (t : Prop)`.
-/

/- Uncommenting breaks it -/
def fails₁ : Prop :=
∀ (x : Foo),
let ⟨foo₁, foo₂⟩ := (foo, foo);
false
-- let_destruct_inside_forall.lean:11:4: error: invalid match/convoy expression, expected type is not known

/- All the following variations fail as well with the same message -/
def fails₂ : Prop :=
∀ (x : Foo),
let (⟨foo₁, foo₂⟩ : Foo × Foo) := (foo, foo);
foo₁ = foo₂

def fails₃ : Prop :=
∀ (x : Foo),
let (⟨foo₁, foo₂⟩ : Foo × Foo) := (foo, foo);
false

def fails₄ : Prop :=
∀ (x : Foo),
let (⟨foo₁, foo₂⟩ : Foo × Foo) := ((foo, foo) : Foo × Foo);
false

def fails₅ : Prop :=
∀ (x : Foo),
let p : Foo × Foo := (foo, foo);
let ⟨foo₁, foo₂⟩ := p;
foo₁ = foo₂
