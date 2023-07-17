/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.OptionIO

namespace Lake

instance [Pure m] : MonadLiftT Id m where
  monadLift act := pure act.run

instance [Alternative m] : MonadLiftT Option m where
  monadLift
    | some a => pure a
    | none => failure

instance [Pure m] [MonadExceptOf ε m] : MonadLiftT (Except ε) m where
  monadLift
    | .ok a => pure a
    | .error e => throw e

instance [Bind m] [MonadReaderOf ρ m] [MonadLiftT n m] : MonadLiftT (ReaderT ρ n) m where
  monadLift act := do act (← read)

instance [Monad m] [MonadStateOf σ m] [MonadLiftT n m] : MonadLiftT (StateT σ n) m where
  monadLift act := do let (a, s) ← act (← get); set s; pure a

instance [Monad m] [Alternative m] [MonadLiftT n m] : MonadLiftT (OptionT n) m where
  monadLift act := act.run >>= liftM

instance [Monad m] [MonadExceptOf ε m] [MonadLiftT n m] : MonadLiftT (ExceptT ε n) m where
  monadLift act := act.run >>= liftM

instance [Monad m] [MonadExceptOf ε m] [MonadLiftT BaseIO m] : MonadLiftT (EIO ε) m where
  monadLift act := act.toBaseIO >>= liftM

instance [Monad m] [Alternative m] [MonadLiftT BaseIO m] : MonadLiftT OptionIO m where
  monadLift act := act.toBaseIO >>= liftM
