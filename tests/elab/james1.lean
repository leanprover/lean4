inductive LazyList (α : Type u)
| nil : LazyList α
| cons (hd : α) (tl : LazyList α) : LazyList α
| delayed (t : Thunk (LazyList α)) : LazyList α

namespace LazyList

def force : LazyList α → Option (α × LazyList α)
| delayed as => force as.get
| nil        => none
| cons a as  => some (a,as)

def length : LazyList α → Nat
| nil        => 0
| cons _ as  => length as + 1
| delayed as => length as.get

theorem F_force_some_len_minus_one {L L' : LazyList α}
  : L.force = some (a, L') → L'.length = L.length - 1
  := sorry

end LazyList

structure LazyBatchQueue (τ) :=
  F : LazyList τ
  F_len : Nat
  h_lens : F.length = F_len

def deq (Q : LazyBatchQueue τ) : Option (τ × LazyBatchQueue τ) :=
  match h:Q.F.force with
  | some (x, F') =>
    some (x,
      ⟨F', Q.F_len - 1,
        by simp [LazyList.F_force_some_len_minus_one h, Q.h_lens]⟩)
  | none => none

theorem deq_correct (Q : LazyBatchQueue τ) : deq Q = none ↔ Q.F.force = none := by
  simp [deq]
  split <;> simp [*]
