import Lean
open Lean Elab Term

elab "foo" t:term "," s:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize t none
  let e2 ← Elab.Term.elabTermAndSynthesize s none
  let t ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) (.app e e2))
  logInfo t
  return e

variable {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
  (H : ∀ (a b : α), r a b → f a = f b)

/-- info: Quot.lift f H @Quot.mk -/
#guard_msgs in
example := foo @Quot.lift.{u, v} α r β f H, @Quot.mk.{u}
