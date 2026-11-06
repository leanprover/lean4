module
import Std

example (l : List Nat) (n : Nat) : l.take (n + 1) = l.take n ++ (l.drop n).take 1 := by
  grind

example (l : List Nat) (a b : Nat) (h : a + b ≤ l.length) :
    (l.take (a + b)).count 0 = (l.take a).count 0 + ((l.drop a).take b).count 0 := by
  grind

example (lst : List Int) (pref : List Nat) (i : Nat) (suff : List Nat)
    (h₁ : ForIn.toList [:lst.length] = pref ++ i :: suff) (found : Bool) (candidate : Int)
    (h₂ : (found = true → candidate ∈ lst ∧ ¬ lst.length / 2 < List.count candidate lst) ∧
      (found = false → ∀ (k : Nat), k < pref.length → ¬ lst.length / 2 < List.count lst[k]! lst))
    (h₃ : ¬ lst.length / 2 < List.count lst[i]! (List.take (ForIn.toList [:lst.length]).length lst))
    (hf : found = false) (x : Nat) (hx : x < (pref ++ [i]).length) :
    ¬ lst.length / 2 < List.count lst[x]! lst := by
  grind
