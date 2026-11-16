import Std.WP
open Lean.Order Std.WP

/-! `PredTrans` is the monad of monotone predicate transformers: the combinators build monotone
transformers, `apply_mono` states the monotonicity of each one, and the supremum of a chain is again a
transformer. -/

example {Q Q' : PUnit → Nat → Prop} (h : Q ⊑ Q') (E : Unit) :
    ((do let s ← get; set (s + 1)) : PredTrans (Nat → Prop) Unit PUnit).apply Q E ⊑
      ((do let s ← get; set (s + 1)) : PredTrans (Nat → Prop) Unit PUnit).apply Q' E :=
  PredTrans.apply_mono _ h PartialOrder.rel_refl

example : ((do let s ← get; set (s + 1)) : PredTrans (Nat → Prop) Unit PUnit).apply
    (fun _ s => s = 4) () 3 := rfl

example {Q : Nat → Prop} {E E' : (String → Prop) × Unit} (h : E ⊑ E') :
    (throw "boom" : PredTrans Prop ((String → Prop) × Unit) Nat).apply Q E ⊑
      (throw "boom" : PredTrans Prop ((String → Prop) × Unit) Nat).apply Q E' :=
  PredTrans.apply_mono _ (PartialOrder.rel_refl) h

noncomputable example {c : PredTrans Prop Unit Nat → Prop} (hc : chain c) :
    PredTrans Prop Unit Nat :=
  CCPO.csup hc

example {c : PredTrans Prop Unit Nat → Prop} (hc : chain c) {pt : PredTrans Prop Unit Nat}
    (h : c pt) : pt ⊑ CCPO.csup hc :=
  le_csup hc h

-- A `WP` instance gives only the transformer; its `wp` is monotone by `PredTrans.apply_mono`.
inductive Toggle where
  | flip

instance : WP Toggle Bool Prop Unit where
  trans _ := ⟨fun Q _ => Q true, fun hQ _ => hQ true⟩

example {Q Q' : Bool → Prop} (h : Q ⊑ Q') : wp Toggle.flip Q () ⊑ wp Toggle.flip Q' () :=
  WP.wp_monotone_post h
