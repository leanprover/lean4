--

structure S  :=
(g {α} : α → α)

def f (h : Nat → ({α : Type} → α → α) × Bool) : Nat :=
(h 0).1 1

def tst : Nat :=
f fun n => (fun x => x, true)

def ex : id (Nat → Nat) :=
by {
  intro;
  assumption
}

def g (i j k : Nat) (a : Array Nat) (h₁ : i < k) (h₂ : k < j) (h₃ : j < a.size) : Nat :=
  let vj := a[j];
  let vi := a[i];
  vi + vj

set_option pp.all true in
#print g

#check g.proof_1

theorem ex1 {p q r s : Prop} : p ∧ q ∧ r ∧ s → r ∧ s ∧ q ∧ p :=
  fun ⟨hp, hq, hr, hs⟩ => ⟨hr, hs, hq, hp⟩

theorem ex2 {p q r s : Prop} : p ∧ q ∧ r ∧ s → r ∧ s ∧ q ∧ p := by
  intro ⟨hp, hq, hr, hs⟩
  exact ⟨hr, hs, hq, hp⟩
