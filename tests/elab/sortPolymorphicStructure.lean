/-!
Tests the auto-generated constructions for a structure whose resulting universe can be `Prop`,
such as `PSigma`. The kernel restricts the recursor of such a type to motives in `Prop`, so
`casesOn`/`recOn`, `sizeOf` and the no-confusion principles are built from projections instead.
-/

set_option bootstrap.inductiveCheckResultingUniverse false in
@[pp_using_anonymous_constructor]
structure Pair {α : Sort u} (β : α → Sort v) : Sort (max u v) where
  mk ::
  fst : α
  snd : β fst

/--
info: recursor Pair.rec.{u, v} : ∀ {α : Sort u} {β : α → Sort v} {motive : Pair β → Prop},
  (∀ (fst : α) (snd : β fst), motive ⟨fst, snd⟩) → ∀ (t : Pair β), motive t
number of parameters: 2
number of indices: 0
number of motives: 1
number of minors: 1
rules:
for Pair.mk (2 fields): fun {α} β motive mk fst snd => mk fst snd
-/
#guard_msgs (whitespace := lax) in
#print Pair.rec

/-- info: @Pair.casesOn : {α : Sort u_2} →
  {β : α → Sort u_3} →
    {motive : Pair β → Sort u_1} → (t : Pair β) → ((fst : α) → (snd : β fst) → motive ⟨fst, snd⟩) → motive t -/
#guard_msgs (whitespace := lax) in
#check @Pair.casesOn

/-- info: @[reducible] def Pair.casesOn.{u_1, u, v} : {α : Sort u} →
  {β : α → Sort v} →
    {motive : Pair β → Sort u_1} → (t : Pair β) → ((fst : α) → (snd : β fst) → motive ⟨fst, snd⟩) → motive t :=
fun {α} {β} {motive} t mk => mk t.1 t.2 -/
#guard_msgs (whitespace := lax) in
#print Pair.casesOn

-- A `Pair` of two propositions is a proposition, and a type otherwise.
example : Prop := Pair (fun _ : True => True)
example : Type := Pair (fun _ : Nat => Nat)

-- The computation rules still hold definitionally.
example : @Pair.casesOn Nat (fun _ => Nat) (fun _ => Nat) ⟨1, 2⟩ (fun a b => a + b) = 3 := rfl
example (x : Pair fun _ : Nat => Nat) :
    x.casesOn (motive := fun _ => Nat) (fun a b => a + b) = x.1 + x.2 := rfl
example : sizeOf (⟨1, 2⟩ : Pair fun _ : Nat => Nat) = 4 := rfl

def add (x : Pair fun _ : Nat => Nat) : Nat :=
  match x with
  | ⟨a, b⟩ => a + b

example : add ⟨1, 2⟩ = 3 := rfl

example (x : Pair fun _ : Nat => Nat) : add x = x.1 + x.2 := by
  cases x
  rfl

example (a b c d : Nat) (h : (⟨a, b⟩ : Pair fun _ : Nat => Nat) = ⟨c, d⟩) : a = c := by
  injection h

-- Elimination into a type out of a `Pair` that is a proposition.
example (x : Pair fun _ : True => True) : Nat :=
  match x with
  | ⟨_, _⟩ => 42

/-!
The library types whose resulting universe can be `Prop`.
-/

example : Prop := PProd True True
example : Type := PProd True Nat
example : Prop := PSigma (fun _ : True => True)
example : Type := PSigma (fun _ : True => Nat)
example : Prop := PULift.{0} True
example : Type := PULift.{1} True
example : Type := PULift.{0} Nat

/-!
`Exists` is a genuine `Prop` with a field that is not a proof, so it has no projections and keeps
its recursor-based `casesOn`.
-/

/-- info: @Exists.casesOn : ∀ {α : Sort u_1} {p : α → Prop} {motive : Exists p → Prop} (t : Exists p),
  (∀ (w : α) (h : p w), motive ⋯) → motive t -/
#guard_msgs (whitespace := lax) in
#check @Exists.casesOn
