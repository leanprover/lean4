set_option grind.warning false

example (as bs cs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        (h₃ : cs = bs)
        (h₄ : i ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  skip
  grind only [= Array.getElem_set_ne, = Array.size_set] -- works

theorem Array.getElem_set_ne_abstracted (xs : Array α) (i : Nat) (h' : i < xs.size) (v : α) {j : Nat}
    (pj : j < xs.size) (h : i ≠ j) :
    (xs.set i v)[j]'(by as_aux_lemma => simp [*]) = xs[j] := Array.getElem_set_ne xs i h' v pj h

example (as bs cs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        (h₃ : cs = bs)
        (h₄ : i ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind only [= Array.getElem_set_ne_abstracted, = Array.size_set] -- should work
