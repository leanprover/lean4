/-- info: fun <other> -/
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

/--
error: unsolved goals
α✝ : Type u_1
a b : List α✝
⊢ List.map (fun x => x) b ++ a = sorry
-/
#guard_msgs in
example : List.foldr (fun x y => x :: y) a b = sorry := by
  simp only [List.foldr_cons_eq_append]

theorem fun_self_eq_id : (fun x : α => x) = id := rfl

/--
error: unsolved goals
m : Type u_1 → Type u_2
α : Type u_1
inst✝¹ : Monad m
inst✝ : LawfulMonad m
x : m α
⊢ id <$> x = sorry
-/
#guard_msgs in
example [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = sorry := by
  simp only [bind_pure_comp, fun_self_eq_id]
