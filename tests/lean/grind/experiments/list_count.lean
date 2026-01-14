-- Things I'd still like to make work for `List.count` via `grind`, but need to move on for now.

open List

variable [BEq α] [LawfulBEq α]

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
