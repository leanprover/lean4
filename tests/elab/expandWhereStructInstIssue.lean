instance [Alternative m] : MonadLiftT Option m where
  monadLift := fun
    | some a => pure a
    | none => failure
