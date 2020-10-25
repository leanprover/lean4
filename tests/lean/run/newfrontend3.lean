

structure S  :=
(g {α} : α → α)

def f (h : Nat → ({α : Type} → α → α) × Bool) : Nat :=
(h 0).1 1

def tst : Nat :=
f fun n => (fun x => x, true)

theorem ex : id (Nat → Nat) :=
by {
  intro;
  assumption
}

def g (i j k : Nat) (a : Array Nat) (h₁ : i < k) (h₂ : k < j) (h₃ : j < a.size) : Nat :=
let vj := a.get ⟨j, h₃⟩;
let vi := a.get ⟨i, Nat.ltTrans h₁ (Nat.ltTrans h₂ h₃)⟩;
vi + vj

set_option pp.all true in
#print g

#check g.proof_1
