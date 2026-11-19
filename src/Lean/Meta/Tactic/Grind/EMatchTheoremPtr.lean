/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.EMatchTheorem
public section
namespace Lean.Meta.Grind

@[inline] def isSameEMatchTheoremPtr (a b : EMatchTheorem) : Bool :=
  unsafe ptrEq a b

structure EMatchTheoremPtr where
  thm : EMatchTheorem

abbrev hashEMatchTheoremPtr (thm : EMatchTheorem) : UInt64 :=
  unsafe (ptrAddrUnsafe thm >>> 3).toUInt64

instance : Hashable EMatchTheoremPtr where
  hash k := hashEMatchTheoremPtr k.thm

instance : BEq EMatchTheoremPtr where
  beq k₁ k₂ := isSameEMatchTheoremPtr k₁.thm k₂.thm

end Lean.Meta.Grind
