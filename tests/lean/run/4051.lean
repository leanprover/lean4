def Array.swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | (i, j) :: ijs =>
    have : (a.swap i j).size = a.size := a.size_swap _ _
    swaps (a.swap i j) (ijs.map (fun p => ⟨⟨p.1.1, by simp⟩, ⟨p.2.1, by simp⟩⟩))
termination_by l => l.length

set_option maxHeartbeats 1000 in
theorem Array.swaps_cancel (a : Array α) (l : List (Fin a.size × Fin a.size)) : a.swaps (l ++ l.reverse) = a :=
  match l with
  | [] => sorry
  | c :: cs =>

    have h : a.size = (a.swaps [c]).size := sorry

    have ih1 : ((a.swaps [c]).swaps ((h ▸ cs) ++ (h ▸ cs).reverse)) = (a.swaps [c]) :=
      swaps_cancel (a.swaps [c]) (h ▸ cs)
    sorry
termination_by l.length
decreasing_by sorry
