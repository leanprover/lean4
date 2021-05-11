namespace TryCatchWithAutolift

structure M (α : Type) where
  σ : ExceptT String IO α

instance : Monad M where
  pure x   := { σ := pure x }
  bind x f := { σ := do (f (← x.σ)).σ }
  map f x  := { σ := do f (← x.σ) }

instance : MonadLiftT IO M where
  monadLift {α : Type} (act : IO α) : M α :=
    { σ := monadLift act }

instance : MonadFinally M where
  tryFinally' := fun x h => M.mk do
    tryFinally' x.σ fun e => (h e).σ

def t : M Unit := do
  liftM $ IO.println "bad"
  try do pure () -- Error
  catch ex : IO.Error => do pure ()
  finally do pure ()

instance : MonadExceptOf IO.Error M where
  throw e := { σ := throwThe IO.Error e }
  tryCatch x handle := { σ := tryCatchThe IO.Error x.σ fun e => handle e |>.σ }

def t2 : M Unit := do
  liftM $ IO.println "bad"
  try do pure ()
  catch ex : IO.Error => do pure ()
  finally do pure ()

end TryCatchWithAutolift
