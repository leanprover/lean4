import Std.WP
open Lean.Order Std.WP

/-! Examples of predicate transformers built with the `PredTrans` API: the monad operations, the
state and exception combinators, `PredTrans.mk`, the supremum of a chain, and a `WP` instance. -/

-- A stateful transformer from `do` notation.
example : ((do let s ← get; set (s + 1)) : PredTrans (Nat → Prop) Unit PUnit).apply
    (fun _ s => s = 4) () 3 := rfl

-- An exception and its handler.
example : (tryCatch (throw 3) (fun e => pure (e + 1)) :
      PredTrans Prop ((Nat → Prop) × Unit) Nat).apply (fun r => r = 4) (fun _ => False, ()) :=
  rfl

-- An exception of an inner layer, caught under an outer exception layer.
example : (tryCatchThe Nat (throwThe Nat 3) (fun e => pure (e + 1)) :
      PredTrans Prop ((String → Prop) × ((Nat → Prop) × Unit)) Nat).apply (fun r => r = 4)
    (fun _ => False, fun _ => False, ()) :=
  rfl

-- A transformer from a monotone function.
def guardZero (P : Prop) : PredTrans Prop Unit Nat :=
  PredTrans.mk (fun Q _ => P ∧ Q 0) fun hQ _ h => ⟨h.1, hQ 0 h.2⟩

example : (guardZero True).apply (fun n => n = 0) () := by
  simp [guardZero]

-- The supremum of a chain of transformers.
noncomputable example {c : PredTrans Prop Unit Nat → Prop} (hc : chain c) :
    PredTrans Prop Unit Nat :=
  CCPO.csup hc

-- A `WP` instance that provides only the transformer.
inductive Toggle where
  | flip

instance : WP Toggle Bool Prop Unit where
  trans _ := PredTrans.mk (fun Q _ => Q true) fun hQ _ => hQ true

example : wp Toggle.flip (fun b => b = true) () := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]
