namespace List

/-
This example exposed a bug in the `grind` internalizer when `grind -revert`
is used.
-/

variable {α : Type} {β : α → Type}

def keys : List (Sigma β) → List α :=
  map Sigma.fst

@[grind =]
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl

variable [DecidableEq α]

def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l

@[grind =]
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl

@[grind =]
theorem dlookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → dlookup a (s :: l) = dlookup a l
  | ⟨_, _⟩, h => dif_neg h.symm

@[grind =]
theorem dlookup_isSome {a : α} {l : List (Sigma β)} : (dlookup a l).isSome ↔ a ∈ l.keys := by
  induction l with
  | nil => sorry
  | cons s _ _ =>
    by_cases a = s.fst
    · grind
    · sorry
