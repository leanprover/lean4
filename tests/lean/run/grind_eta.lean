module
reset_grind_attrs%
example {l : List α} {f : β → α → β} {b : β} :
    l.foldl f b = l.reverse.foldr (fun x y => f y x) b := by
  grind [List.foldr_reverse]

/-
The following example doesn't work yet. `grind` doesn't have a mechanism
for inferring that `fun x y => g y x` is equal to `f` given
the equality `g = (f x y => f y x)`
-/
-- example {l : List α} {f : β → α → β} {b : β} :
--    g = (fun x y => f y x) → l.foldl f b = l.reverse.foldr g b := by
--  grind [List.foldr_reverse]
