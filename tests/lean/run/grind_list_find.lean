open List

theorem findSome?_eq_none_iff : findSome? p l = none ↔ ∀ x ∈ l, p x = none := by
  induction l with grind

theorem findSome?_isSome_iff {f : α → Option β} {l : List α} :
    (l.findSome? f).isSome ↔ ∃ x, x ∈ l ∧ (f x).isSome := by
  induction l with grind

attribute [grind] Option.isSome_iff_ne_none -- Can we add this?

theorem Sublist.findSome?_eq_none {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    l₂.findSome? f = none → l₁.findSome? f = none := by
  grind

theorem IsPrefix.findSome?_eq_none {l₁ l₂ : List α} {f : α → Option β} (h : l₁ <+: l₂) :
    List.findSome? f l₂ = none → List.findSome? f l₁ = none := by
  grind

theorem find?_flatten_eq_none_iff {xs : List (List α)} {p : α → Bool} :
    xs.flatten.find? p = none ↔ ∀ ys ∈ xs, ∀ x ∈ ys, !p x := by
  grind

theorem find?_flatMap_eq_none_iff {xs : List α} {f : α → List β} {p : β → Bool} :
    (xs.flatMap f).find? p = none ↔ ∀ x ∈ xs, ∀ y ∈ f x, !p y := by
  grind

theorem find?_replicate_eq_some_iff {n : Nat} {a b : α} {p : α → Bool} :
    (replicate n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  grind

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

example (xs : List Nat) (h : 3 ∈ xs) : (xs.find? (· ≤ 5)).isSome := by grind
example (xs : List Nat) (h : 3 ∈ xs) : xs.findIdx (· ≤ 5) < xs.length := by grind
example (xs : List Nat) (h : 3 ∈ xs) : xs[xs.findIdx (· ≤ 5)] < 7 := by grind
example (xs : List Nat) (h : 3 ∈ xs) : xs[xs.findIdx (· ≤ 5)] < 5 + xs.length := by grind
example (xs : List Nat) (h : 3 ∈ xs) : xs[xs.findIdx (· ≤ 5)] = 4 → 2 ≤ xs.length := by
  grind [cases List]

example (xs : List Nat) (h : ∀ x, x ∈ xs → x > 7) : xs.find? (· ≤ 5) = none := by grind
example (xs : List Nat) (h : ∀ x, x ∈ xs → x > 7) : xs.findIdx (· ≤ 5) = xs.length := by grind

/-- If `¬ p xs[j]` for all `j < i`, then `i ≤ xs.findIdx p`. -/
theorem le_findIdx_of_not {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.length)
    (h2 : ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false) : i ≤ xs.findIdx p := by
  grind

/-- If `¬ p xs[j]` for all `j ≤ i`, then `i < xs.findIdx p`. -/
theorem lt_findIdx_of_not {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.length)
    (h2 : ∀ j (hji : j ≤ i), ¬p (xs[j]'(Nat.lt_of_le_of_lt hji h))) : i < xs.findIdx p := by
  grind

theorem Sublist.findIdx?_isSome {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    (l₁.findIdx? p).isSome → (l₂.findIdx? p).isSome := by
  grind
