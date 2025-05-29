-- Things I'd still like to make work for `List.count` via `grind`, but need to move on for now.

open List

example (hx : x = 0) (hy : y = 0) (hz : z = 0) : x = y + z := by grind -- cutsat bug

theorem length_eq_countP_add_countP (p : α → Bool) {l : List α} : length l = countP p l + countP (fun a => ¬p a) l := by
  induction l with grind -- failing because of cutsat bug

variable [BEq α] [LawfulBEq α]

theorem count_flatten {a : α} {l : List (List α)} : count a l.flatten = (l.map (count a)).sum := by
  grind (ematch := 10) (gen := 10) -- fails

theorem count_concat_self {a : α} {l : List α} : count a (concat l a) = count a l + 1 := by grind [concat_eq_append] -- fails?!

theorem count_eq_length {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  induction l with grind

theorem _root_.List.getElem_filter {xs : List α} {p : α → Bool} {i : Nat} (h : i < (xs.filter p).length) :
    p (xs.filter p)[i] := sorry

theorem _root_.List.getElem?_filter {xs : List α} {p : α → Bool} {i : Nat} (h : i < (xs.filter p).length)
    (w : (xs.filter p)[i]? = some a) : p a := sorry

attribute [grind?] List.getElem_filter
grind_pattern List.getElem?_filter => (xs.filter p)[i]?, some a

theorem filter_beq {l : List α} (a : α) : l.filter (· == a) = replicate (count a l) a := by
  ext
  grind

theorem filter_eq [DecidableEq α] {l : List α} (a : α) : l.filter (· = a) = replicate (count a l) a := by
  grind
