-- Things I'd still like to make work for `List.count` via `grind`, but need to move on for now.

open List


variable [BEq α] [LawfulBEq α]

theorem filter_beq {l : List α} (a : α) : l.filter (· == a) = replicate (count a l) a := by
  ext
  grind

theorem count_flatten {a : α} {l : List (List α)} : count a l.flatten = (l.map (count a)).sum := by
  grind (ematch := 10) (gen := 10) -- fails

theorem count_concat_self {a : α} {l : List α} : count a (concat l a) = count a l + 1 := by grind [concat_eq_append] -- fails?!

theorem count_eq_length {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  induction l with grind

theorem filter_eq [DecidableEq α] {l : List α} (a : α) : l.filter (· = a) = replicate (count a l) a := by
  grind

theorem replicate_count_eq_of_count_eq_length {l : List α} (h : count a l = length l) :
    replicate (count a l) a = l := by
  grind

theorem count_filterMap {α} [BEq β] {b : β} {f : α → Option β} {l : List α} :
    count b (filterMap f l) = countP (fun a => f a == some b) l := by
  grind

theorem count_flatMap {α} [BEq β] {l : List α} {f : α → List β} {x : β} :
    count x (l.flatMap f) = sum (map (count x ∘ f) l) := by
  grind
