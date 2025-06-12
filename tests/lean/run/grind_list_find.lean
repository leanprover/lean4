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
