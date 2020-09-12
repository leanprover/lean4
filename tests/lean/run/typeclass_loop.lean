new_frontend

example (M : Type → Type) [Monad M] : ExceptT Unit (ReaderT Unit (StateT Unit M)) Unit := do
ctx ← read;
pure ()
