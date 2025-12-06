/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadCanon
public section
namespace Lean.Meta.Grind.Arith.CommRing

class MonadSemiring (m : Type → Type) where
  getSemiring : m Semiring
  modifySemiring : (Semiring → Semiring) → m Unit

export MonadSemiring (getSemiring modifySemiring)

@[always_inline]
instance (m n) [MonadLift m n] [MonadSemiring m] : MonadSemiring n where
  getSemiring    := liftM (getSemiring : m Semiring)
  modifySemiring f := liftM (modifySemiring f : m Unit)

class MonadCommSemiring (m : Type → Type) where
  getCommSemiring : m CommSemiring
  modifyCommSemiring : (CommSemiring → CommSemiring) → m Unit

export MonadCommSemiring (getCommSemiring modifyCommSemiring)

@[always_inline]
instance (m n) [MonadLift m n] [MonadCommSemiring m] : MonadCommSemiring n where
  getCommSemiring      := liftM (getCommSemiring : m CommSemiring)
  modifyCommSemiring f := liftM (modifyCommSemiring f : m Unit)

@[always_inline]
instance (m) [Monad m] [MonadCommSemiring m] : MonadSemiring m where
  getSemiring := return (← getCommSemiring).toSemiring
  modifySemiring f := modifyCommSemiring fun s => { s with toSemiring := f s.toSemiring }

end Lean.Meta.Grind.Arith.CommRing
