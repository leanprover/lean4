theorem ex1 [Monad m] [LawfulMonad m] (b : Bool) (ma : m α) (mb : α → m α) :
    (do let mut x ← ma
        if b then
          x ← mb x
        pure x)
    =
    (ma >>= fun x => if b then mb x else pure x) := by
  cases b <;> simp

attribute [simp] seq_eq_bind_map

theorem ex2 [Monad m] [LawfulMonad m] (b : Bool) (ma : m α) (mb : α → m α) (a : α) :
    (do let mut x ← ma
        if b then
          x ← mb x
        pure x)
    =
    (StateT.run' (m := m)
      (do ma >>= set
          if b then get >>= fun x => mb x >>= set
          get) a)  := by
  cases b <;> simp
