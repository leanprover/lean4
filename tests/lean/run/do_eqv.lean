theorem byCases_Bool_bind [Monad m] (x : m Bool) (f g : Bool → m β) (isTrue : f true = g true) (isFalse : f false = g false) : (x >>= f) = (x >>= g) := by
  have f = g by
    funext b
    cases b with
    | true  => exact isTrue
    | false => exact isFalse
  rw [this]

theorem eq_findM [Monad m] [LawfulMonad m] (p : α → m Bool) (xs : List α) :
    (do for x in xs do
          let b ← p x
          if b then
            return some x
        return none)
    =
    xs.findM? p := by
  induction xs with
  | nil => simp [List.findM?]
  | cons x xs ih =>
    simp [List.findM?]; rw[← ih]; simp
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
  induction xss with
  | nil => simp [List.findSomeM?]
  | cons xs xss ih =>
    simp [List.findSomeM?]
    rw [← ih, ← eq_findM]
    induction xs with
    | nil => simp
    | cons x xs ih => simp; apply byCases_Bool_bind <;> simp [ih]
