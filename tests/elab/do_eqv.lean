theorem byCases_Bool_bind [Monad m] (x : m Bool) (f g : Bool → m β) (isTrue : f true = g true) (isFalse : f false = g false) : (x >>= f) = (x >>= g) := by
  have : f = g := by
    funext b; cases b <;> assumption
  rw [this]

theorem eq_findM [Monad m] [LawfulMonad m] (p : α → m Bool) (xs : List α) :
    (do for x in xs do
          let b ← p x
          if b then
            return some x
        return none)
    =
    xs.findM? p := by
  induction xs with simp [List.findM?]
  | cons x xs ih =>
    rw [← ih]; simp
    apply byCases_Bool_bind <;> simp

theorem eq_findSomeM_findM [Monad m] [LawfulMonad m] (p : α → m Bool) (xss : List (List α)) :
    (do for xs in xss do
           for x in xs do
             let b ← p x
             if b then
               return some x
        return none)
    =
    xss.findSomeM? (fun xs => xs.findM? p) := by
  induction xss with simp [List.findSomeM?]
  | cons xs xss ih =>
    rw [← ih, ← eq_findM]
    induction xs with simp
    | cons x xs ih =>
      apply byCases_Bool_bind <;> simp [ih]

theorem eq_findSomeM_findM' [Monad m] [LawfulMonad m] (p : α → m Bool) (xss : List (List α)) :
    (do for xs in xss do
           for x in xs do
             let b ← p x
             if b then
               return some x
        return none)
    =
    xss.findSomeM? (fun xs => xs.findM? p) := by
  induction xss <;> simp [List.findSomeM?]
  rename List α => xs
  rename _ = _  => ih
  rw [← ih, ← eq_findM]
  induction xs <;> simp
  rename _ = _ => ih
  apply byCases_Bool_bind <;> simp [ih]

theorem z_add (x : Nat) : 0 + x = x := by
  induction x
  rfl
  rename _ = _ => ih
  show Nat.succ (0 + _) = _
  rw [ih]
