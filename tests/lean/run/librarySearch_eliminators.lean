/-
Test that exact? finds "eliminator-style" theorems like iteInduction
where the conclusion has an fvar head: `motive (C args...)`.

These theorems are indexed by their first argument's const head (e.g., `ite`),
allowing them to be found even with `-star` (when generic star-indexed lemmas are excluded).
-/

-- Test that exact? finds iteInduction for fvar-headed goals
example {α : Sort u} (h : Prop) [Decidable h] {x y : α} {p : α → Prop}
    (hx : h → p x) (hy : ¬h → p y) : p (if h then x else y) := by
  exact iteInduction hx hy

/--
info: Try this:
  [apply] exact iteInduction hx hy
-/
#guard_msgs in
example {α : Sort u} (h : Prop) [Decidable h] {x y : α} {p : α → Prop}
    (hx : h → p x) (hy : ¬h → p y) : p (if h then x else y) := by
  exact?

-- Test that iteInduction is found even with -star (via secondary const-keyed index)
/--
info: Try this:
  [apply] exact iteInduction hx hy
-/
#guard_msgs in
example {α : Sort u} (h : Prop) [Decidable h] {x y : α} {p : α → Prop}
    (hx : h → p x) (hy : ¬h → p y) : p (if h then x else y) := by
  exact? -star
