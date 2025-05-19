/-- info: fun _ -/
#guard_msgs in
#discr_tree_key fun x => x

/-- info: @bind _ _ _ _ _ (fun @pure _ _ _ _) -/
#guard_msgs in
#discr_tree_simp_key bind_pure_comp

/-- info: @List.foldlM _ _ _ _ (fun fun @pure _ _ _ _) _ _ -/
#guard_msgs in
#discr_tree_simp_key List.foldlM_pure

/-- info: @List.foldr _ (List _) (fun @List.cons _ _) _ _ -/
#guard_msgs in
#discr_tree_simp_key List.foldr_cons_eq_append

/-- info: @Eq Sort _ _ -/
#guard_msgs in
#discr_tree_key propext

/--
error: unsolved goals
a b : List Nat
⊢ List.map (fun x => x + 1) b ++ a = sorry
-/
#guard_msgs in
example : List.foldr (fun x y => (x + 1) :: y) a b = sorry := by
  simp only [List.foldr_cons_eq_append]

theorem fun_self_eq_id : (fun x : α => x) = id := rfl

example : (fun x : { a // a < 5 } => ⟨x.1, x.2⟩) = id := by
  simp only [fun_self_eq_id]

/--
error: unsolved goals
m : Type → Type u_1
inst✝¹ : Monad m
inst✝ : LawfulMonad m
x : m Nat
⊢ Nat.succ <$> x = sorry
-/
#guard_msgs in
example [Monad m] [LawfulMonad m] (x : m Nat) : x >>= (fun y => pure y.succ) = sorry := by
  simp only [bind_pure_comp]

/--
error: unsolved goals
⊢ List.foldl HAdd.hAdd 1 (List.map Nat.succ [1, 2, 3]) = sorry
-/
#guard_msgs in
example : List.foldl (· + ·.succ) 1 [1, 2, 3] = sorry := by
  simp only [← List.foldl_map]

/--
error: unsolved goals
⊢ [(1, 2), (3, 4)] = sorry
-/
#guard_msgs in
example : List.map (fun x => (x.1, x.2)) [(1, 2), (3, 4)] = sorry := by
  simp only [List.map_id']
