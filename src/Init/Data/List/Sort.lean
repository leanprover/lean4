import Lean

section
open Lean Elab Command

syntax (name := timeCmd) "#time " command : command

/--
Time the elaboration of a command, and print the result (in milliseconds).

Example usage:
```
set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
```
-/
@[command_elab timeCmd] def timeCmdElab : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end

namespace List

def split : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: as =>
    let (l, r) := split as
    (a :: l, b :: r)

@[simp] theorem split_nil : split ([] : List α) = ([], []) := rfl
@[simp] theorem split_singleton (a : α) : split [a] = ([a], []) := rfl
@[simp] theorem split_cons_cons (a b : α) (as : List α) : split (a :: b :: as) = (a :: (split as).1, b :: (split as).2) := rfl

theorem split_fst_length : (l : List α) → (split l).1.length = (l.length + 1) / 2
  | [] | [_] | a :: b :: as => by simp [split, split_fst_length] <;> omega

theorem split_snd_length : (l : List α) → (split l).2.length = l.length / 2
  | [] | [_] | a :: b :: as => by simp [split, split_snd_length] <;> omega

def merge (lt : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if lt x y then
      x :: merge lt xs (y :: ys)
    else
      y :: merge lt (x :: xs) ys

@[simp] theorem merge_nil (lt : α → α → Bool) (xs : List α) : merge lt xs [] = xs := by
  cases xs <;> simp [merge]

def mergeSort (lt : α → α → Bool) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: xs =>
    let lr := split (a :: b :: xs)
    have := split_fst_length xs
    have := split_snd_length xs
    merge lt (lr.1.mergeSort lt) (lr.2.mergeSort lt)
  termination_by l => l.length

theorem mem_merge (lt : α → α → Bool) {a : α} : (xs ys : List α) → a ∈ merge lt xs ys ↔ a ∈ xs ∨ a ∈ ys
  | [], ys => by simp [merge]
  | xs, [] => by simp [merge]
  | x :: xs, y :: ys => by
    simp [merge]
    split <;> rename_i h
    · simp only [mem_cons, mem_merge lt xs (y :: ys), or_assoc]
    · simp only [mem_cons, mem_merge lt (x :: xs) ys, ← or_assoc]
      apply or_congr_left
      rw [or_comm (a := a = y), or_assoc, or_assoc]
      apply or_congr_right
      rw [or_comm]

theorem mem_of_mem_split_fst {a : α} {l : List α} : a ∈ (split l).1 → a ∈ l := by
  sorry
theorem mem_of_mem_split_snd {a : α} {l : List α} : a ∈ (split l).2 → a ∈ l := by
  sorry

theorem split_fst_sublist (l : List α) : (split l).1 <+ l := by
  sorry
theorem split_snd_sublist (l : List α) : (split l).2 <+ l := by
  sorry

def sorted (lt : α → α → Bool) (xs : List α) : Prop := xs.Pairwise fun a b => !lt b a

variable (lt : α → α → Bool)

theorem split_fst_sorted : (l : List α) → sorted lt l → sorted lt (split l).1
  | [], h => by simpa [split]
  | [a], h => by simpa [split]
  | a :: b :: as, h => by
    simp [split]
    constructor
    · cases h
      rename_i h
      intro z m
      exact h z (mem_cons.mpr (Or.inr (mem_of_mem_split_fst m)))
    · cases h
      rename_i h w
      exact h.tail.sublist (split_fst_sublist as)

theorem split_snd_sorted : (l : List α) → sorted lt l → sorted lt (split l).2
  | [], h => by simpa [split]
  | [a], h => by simp [split, sorted]
  | a :: b :: as, h => by
    simp [split]
    constructor
    · cases h
      rename_i h
      intro z m
      sorry
    · cases h
      rename_i h w
      exact h.tail.sublist (split_snd_sublist as)

theorem merge_split_of_sorted : (l : List α) → sorted lt l → merge lt (split l).1 (split l).2 = l
  | [], _ => sorry
  | [a], _ => sorry
  | a :: b :: as, h => by
    simp [merge]
    have := split_fst_length as
    have := split_snd_length as
    rw [if_pos]
    sorry
    sorry

theorem merge_split_cons_of_sorted : (b : α) → (as : List α) → sorted lt (b :: as) → merge lt (split as).1 (b :: (split as).2) = b :: as := by
  sorry


section
variable (antisymm : ∀ a b, lt a b → !lt b a) (trans : ∀ a b c, lt a b → lt b c → lt a c)
    (total : ∀ a b, a ≠ b → !lt a b → lt b a)
include antisymm trans total

theorem merge_sorted :
    {xs ys : List α} → sorted lt xs → sorted lt ys → sorted lt (merge lt xs ys)
  | [], ys, _, h => by simpa [merge]
  | xs, [], h, _ => by simpa [merge]
  | x :: xs, y :: ys, h₁, h₂ => by
    simp [merge]
    split <;> rename_i xy
    · constructor
      · intro z m
        simp only [Bool.not_eq_true']
        simp [mem_merge] at m
        rcases m with m | rfl | m
        · have := rel_of_pairwise_cons h₁ m
          apply Decidable.byContradiction
          intro zx
          specialize trans _ _ _ (by simpa using zx) xy
          simp_all
        · specialize antisymm x z
          simp_all
        · have := rel_of_pairwise_cons h₂ m
          simp at this
          specialize antisymm _ _ xy
          apply Decidable.byContradiction
          intro zx
          specialize trans _ _ _ (by simpa using zx) xy
          simp_all
      · exact merge_sorted h₁.tail h₂
    · constructor
      · intro z m
        simp only [Bool.not_eq_true']
        simp [mem_merge] at m
        rcases m with (rfl | m) | m
        · simpa using xy
        · have := rel_of_pairwise_cons h₁ m
          apply Decidable.byContradiction
          intro zy
          by_cases xy' : x = y
          · simp_all
          · specialize total _ _ xy' (by simpa using xy)
            specialize trans _ _ _ (by simpa using zy) total
            simp_all
        · have := rel_of_pairwise_cons h₂ m
          apply Decidable.byContradiction
          intro zy
          simp_all
      · exact merge_sorted h₁ h₂.tail

theorem mergeSort_sorted : (xs : List α) → sorted lt (mergeSort lt xs)
  | []
  | [a] => by simp [mergeSort, sorted]
  | a :: b :: xs => by
    simp [mergeSort]
    apply merge_sorted lt antisymm trans total
    · have := split_fst_length xs
      apply mergeSort_sorted
    · have := split_snd_length xs
      apply mergeSort_sorted
termination_by l => l.length

theorem mergeSort_eq_self_of_sorted : (xs : List α) → sorted lt xs → mergeSort lt xs = xs
  | [], _ => sorry
  | [a], _ => sorry
  | a :: b :: xs, h => by
    simp [mergeSort]
    have := split_fst_length xs
    have := split_snd_length xs
    rw [mergeSort_eq_self_of_sorted]
    rw [mergeSort_eq_self_of_sorted]
    rw [merge, if_pos sorry, merge_split_cons_of_sorted]
    exact h.tail
    sorry
    sorry
  termination_by l => l.length

theorem mergeSort_mergeSort (xs : List α) : mergeSort lt (mergeSort lt xs) = mergeSort lt xs :=
  mergeSort_eq_self_of_sorted lt antisymm trans total (mergeSort lt xs) (mergeSort_sorted lt antisymm trans total xs)

#eval! mergeSort (· < ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

-- Stack overflow at 10000.
#eval! (mergeSort (· < ·) (List.range 1000)).length

def splitRev (l : List α) : List α × List α :=
  go l [] []
where go : List α → List α → List α → List α × List α
  | [], l₁, l₂ => (l₁, l₂)
  | [a], l₁, l₂ => (a :: l₁, l₂)
  | a :: b :: as, l₁, l₂ =>
    go as (a :: l₁) (b :: l₂)

#eval splitRev [1,2,3,4,5,6]

theorem splitRev_go_fst_length : (l l₁ l₂ : List α) → (splitRev.go l l₁ l₂).1.length = (l.length + 1) / 2 + l₁.length
| [], _, _
| [_], _, _ => by simp [splitRev.go] <;> omega
| a :: b :: as, l₁, l₂ => by
  simp only [splitRev.go]
  rw [splitRev_go_fst_length as (a :: l₁) (b :: l₂)]
  simp
  omega

theorem splitRev_go_snd_length : (l l₁ l₂ : List α) → (splitRev.go l l₁ l₂).2.length = l.length / 2 + l₂.length
| [], _, _
| [_], _, _ => by simp [splitRev.go]
| a :: b :: as, l₁, l₂ => by
  simp only [splitRev.go]
  have := splitRev_go_snd_length as (a :: l₁) (b :: l₂)
  rw [this]
  simp
  omega

theorem splitRev_go_fst_length_le (l l₁ l₂ : List α) : (splitRev.go l l₁ l₂).1.length ≤ l.length + l₁.length := by
  have := splitRev_go_fst_length l l₁ l₂
  omega

theorem splitRev_go_snd_length_le (l l₁ l₂ : List α) : (splitRev.go l l₁ l₂).2.length ≤ l.length + l₂.length := by
  have := splitRev_go_snd_length l l₁ l₂
  omega

@[simp] theorem splitRev_cons_cons_fst_length (a b : α) (as : List α) : (splitRev (a :: b :: as)).1.length = (splitRev as).1.length + 1 := by
  simp [splitRev, splitRev_go_fst_length]
  omega

@[simp] theorem splitRev_cons_cons_snd_length (a b : α) (as : List α) : (splitRev (a :: b :: as)).2.length = (splitRev as).2.length + 1 := by
  simp [splitRev, splitRev_go_snd_length]
  omega

theorem splitRev_fst_length_le (l : List α) : (splitRev l).1.length ≤ l.length := by
  simp [splitRev]
  have := splitRev_go_fst_length_le l [] []
  simp at this
  omega

theorem splitRev_snd_length_le (l : List α) : (splitRev l).2.length ≤ l.length := by
  simp [splitRev]
  have := splitRev_go_snd_length_le l [] []
  simp at this
  omega

def merge2 (s : α → α → Prop) [DecidableRel s] (l₁ l₂ : List α) : List α :=
  go l₁ l₂ []
where go : List α → List α → List α → List α
  | [], l₂, acc => acc.reverse ++ l₂
  | l₁, [], acc => acc.reverse ++ l₁
  | x :: xs, y :: ys, acc =>
    if s x y then
      go xs (y :: ys) (x :: acc)
    else
      go (x :: xs) ys (y :: acc)

#eval merge2 (· < ·) [1, 3, 5] [2, 4, 6]

def mergeSort2 (s : α → α → Prop) [DecidableRel s] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: xs  =>
    let lr := splitRev (a :: b :: xs)
    have := splitRev_fst_length_le xs
    have := splitRev_snd_length_le xs
    merge2 s (lr.1.mergeSort2 s) (lr.2.mergeSort2 s)
termination_by l => l.length

#eval! mergeSort2 (· < ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

-- 1 * 10^6: 3.9ms
-- 2 * 10^6: 9.8ms
-- 3 * 10^6: 12.8s
-- #time
-- #eval! (mergeSort2 (· < ·) (List.range (3 * 10^6))).length

-- crashes between 10^5 and 10^6
#eval (Array.qsort (List.range (1 * 10^5)).toArray fun a b => a < b).size

end List
