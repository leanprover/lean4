def List.bubblesort [LT α] [DecidableLT α] (l : List α) : {l' : List α // l.length = l'.length} :=
  match l with
  | [] => ⟨[], rfl⟩
  | x :: xs =>
    match bubblesort xs with
    | ⟨[], h⟩ => ⟨[x], by simp[h]⟩
    | ⟨y :: ys, h⟩ =>
      if y < x then
        have : Nat.succ (length ys) < Nat.succ (length xs) := by rw [h, List.length_cons]; apply Nat.lt_succ_self
        let ⟨zs, he⟩ := bubblesort (x :: ys)
        ⟨y :: zs, by simp[h, ← he]⟩
      else
        ⟨x :: y :: ys, by simp[h]⟩
termination_by l.length
