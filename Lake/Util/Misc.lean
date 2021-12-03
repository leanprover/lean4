/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

def liftOption [Alternative m] : Option α → m α
| some a => pure a
| none => failure

instance [MonadLiftT m n] : MonadLiftT (ReaderT ρ m) (ReaderT ρ n) where
  monadLift x := fun r => liftM <| x r
