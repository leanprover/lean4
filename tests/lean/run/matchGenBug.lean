theorem foo (x : Nat) (h : x > 0) : x ≠ 0 :=
  match x with
  | 0   => sorry
  | h+1 => sorry

inductive Mem : α → List α → Prop where
 | head (a : α) (as : List α)   : Mem a (a::as)
 | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)
infix:50 "∈" => Mem

theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  induction as with
  | nil          => cases h
  | cons b bs ih => cases h with
    | head a bs => exact ⟨[], ⟨bs, rfl⟩⟩
    | tail a b bs h =>
      match bs, ih h with
      | _, ⟨s, t, rfl⟩ =>
        exists b::s; exists t
        rw [List.cons_append]
