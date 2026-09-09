/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Init.Classical
public import Init.Ext
import Init.Grind.Attr

public section

/-- A value hidden from compiled code. `Erased.mk 42` erases to a dummy at runtime, and
proofs recover the `42` as `(Erased.mk 42).out`. -/
@[expose] def Erased (α : Sort u) : Sort (max 1 u) :=
  { s : α → Prop // ∃ a, (a = ·) = s }

namespace Erased

/-- Hides `a` in an `Erased α`. Compiled code drops the argument. -/
@[expose, macro_inline] def mk {α : Sort u} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- The value hidden in `e`, available to proofs only. -/
noncomputable def out {α : Sort u} (e : Erased α) : α :=
  Classical.choose e.property

@[simp, grind =] theorem out_mk {α : Sort u} (a : α) : (mk a).out = a :=
  cast (congrFun (Classical.choose_spec (mk a).property) a).symm rfl

@[simp, grind =] theorem mk_out {α : Sort u} (e : Erased α) : mk e.out = e := by
  cases e with
  | mk s h => exact Subtype.ext (Classical.choose_spec h)

@[ext] theorem out_inj {α : Sort u} {a b : Erased α} (h : a.out = b.out) : a = b := by
  rw [← mk_out a, ← mk_out b, h]

@[simp, grind] theorem mk_inj {α : Sort u} {a b : α} : mk a = mk b ↔ a = b :=
  ⟨fun h => by have := congrArg out h; rwa [out_mk, out_mk] at this, fun h => h ▸ rfl⟩

end Erased
