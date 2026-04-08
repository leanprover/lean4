import Lean.Meta.Basic

open Lean

instance [Monad m] [MonadLiftT MetaM m] : MonadLiftT (ST IO.RealWorld) m where
  monadLift x := (x : MetaM _)
