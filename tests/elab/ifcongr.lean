--
@[simp] theorem andTrue (p : Prop) : (p ∧ True) = p :=
  propext <| Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, trivial⟩)
attribute [simp] Nat.add_comm

theorem ex1 (x : Nat) : (if x > 3 ∧ True then 1 else 2) = (if x > 3 then 1 else 2) :=
 by simp

theorem ex2 (x : Nat) : (if x = 0 ∧ True then x + 1 else 2 + x) = (if x = 0 then 1 else x + 2) :=
  by simp (config := {contextual := true})

#print ex2

theorem ex3 (x : Nat) : (if h : x = 0 ∧ True then x + 1 else 2 + x) = (if h : x = 0 then 1 + x else x + 2) :=
  by simp

#print ex3
