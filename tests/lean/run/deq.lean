inductive LazyList (α : Type u)
| nil : LazyList α
| cons (hd : α) (tl : LazyList α) : LazyList α
| delayed (t : Thunk (LazyList α)) : LazyList α

namespace LazyList

def force : LazyList α → Option (α × LazyList α)
| delayed as => force as.get
| nil        => none
| cons a as  => some (a,as)

end LazyList

def deq (Q : LazyList τ) : Option (τ × LazyList τ) :=
  match h:Q.force with
  | some (x, F') => some (x, F')
  | none => none

theorem deq_correct_1 (Q : LazyList τ)
  : deq Q = none ↔ Q.force = none
  := by
    unfold deq
    cases h' : Q.force <;> simp

theorem deq_correct_2 (Q : LazyList τ)
  : deq Q = none ↔ Q.force = none
  := by
    cases h' : Q.force with
    | none => unfold deq; rw [h']; simp
    | some => unfold deq; rw [h']; simp

theorem deq_correct_3 (Q : LazyList τ)
  : deq Q = none ↔ Q.force = none
  := by
    cases h' : Q.force <;> unfold deq <;> rw [h'] <;> simp
