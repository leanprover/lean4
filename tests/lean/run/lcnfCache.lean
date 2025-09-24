def List.pwFilter {α} (R : α → α → Prop) [DecidableRel R] (l : List α) : List α :=
  l.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) []

def List.dedup {α} [DecidableEq α] : List α → List α :=
  List.pwFilter (· ≠ ·)

def Multiset.{u} : Type u → Type u :=
  fun α => Quotient (List.isSetoid α)

def Multiset.ofList {α} : List α → Multiset α :=
  Quot.mk _

def Multiset.map {α β} (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => Multiset.ofList (l.map f)) fun _l₁ _l₂ p => Quot.sound (p.map f)

def Multiset.dedup {α} [DecidableEq α] (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => Multiset.ofList l.dedup) fun l₁ l₂ p => Quot.sound (by sorry)

def Multiset.card {α} : Multiset α → Nat := Quot.lift List.length fun _l₁ _l₂ => List.Perm.length_eq

def test (_ : Unit) : Bool :=
  let m := Multiset.ofList [0, 1]
  let m := Multiset.map (fun i => i) m
  let m := m.dedup
  m.card < 2

/--
error: Tactic `native_decide` evaluated that the proposition
  (let p := fun i => i;
      (Multiset.map (fun i => i) (Multiset.ofList [0, 1])).dedup).card <
    2
is false
-/
#guard_msgs in
theorem claim :
  ( let p : Nat → Nat := fun i => i;
    (Multiset.map (fun i => i) (Multiset.ofList [0,1])).dedup).card < 2  := by
  native_decide
