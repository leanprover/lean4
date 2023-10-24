import Lean
open Lean Elab Term

elab "foo" t:term "," s:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize t none
  let e2 ← Elab.Term.elabTermAndSynthesize s none
  let t ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) (.app e e2))
  println! t
  return e

variable {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
  (H : ∀ (a b : α), r a b → f a = f b)
example := foo @Quot.lift.{u, v} α r β f H, @Quot.mk.{u}
