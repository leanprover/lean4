/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

instance (priority := low) [Monad m] [MonadExceptOf PUnit m] : Alternative m where
  failure := throw ()
  orElse := tryCatch

/-- Ensure direct lifts are preferred over indirect ones. -/
instance (priority := high) [MonadLift α β] : MonadLiftT α β := ⟨MonadLift.monadLift⟩

instance (priority := low) [Pure m] : MonadLiftT Id m where
  monadLift act := pure act.run

instance (priority := low) [Alternative m] : MonadLiftT Option m where
  monadLift
    | some a => pure a
    | none => failure

instance (priority := low) [Pure m] [MonadExceptOf ε m] : MonadLiftT (Except ε) m where
  monadLift
    | .ok a => pure a
    | .error e => throw e

-- Remark: not necessarily optimal; uses context non-linearly
instance (priority := low) [Bind m] [MonadReaderOf ρ m] [MonadLiftT n m] : MonadLiftT (ReaderT ρ n) m where
  monadLift act := do act (← read)

-- Remark: not necessarily optimal; uses state non-linearly
instance (priority := low) [Monad m] [MonadStateOf σ m] [MonadLiftT n m] : MonadLiftT (StateT σ n) m where
  monadLift act := do let (a, s) ← act (← get); set s; pure a

instance (priority := low) [Monad m] [Alternative m] [MonadLiftT n m] : MonadLiftT (OptionT n) m where
  monadLift act := act.run >>= liftM

instance (priority := low) [Monad m] [MonadExceptOf ε m] [MonadLiftT n m] : MonadLiftT (ExceptT ε n) m where
  monadLift act := act.run >>= liftM

instance (priority := low) [Monad m] [MonadExceptOf ε m] [MonadLiftT BaseIO m] : MonadLiftT (EIO ε) m where
  monadLift act := act.toBaseIO >>= liftM
