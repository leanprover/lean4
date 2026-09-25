/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Heyting
public import Std.Internal.Order.FrameClosure

public section

/-!
# Automation for the lattice theory

This module registers the automation lemmas of the lattice theory with `simp` and `grind norm`.
A lemma gets both attributes if and only if it is an unconditional equation (or `Iff`) whose right
side removes lattice vocabulary, moves it to a smaller carrier (pointwise application, pair
components), or moves it into the `Prop` argument of `⌜·⌝`. Such an equation holds in every
context, including under binders, and rewriting with the whole set terminates.

`grind` rewrites with `grind norm` lemmas while it preprocesses the goal, before E-matching, and it
rewrites under binders. For example, at carrier `Prop` the hypothesis
```
h : ¬ ⨆ r, ⌜some false = some r⌝ ⊓ (r = false ∧ q)
```
normalizes to `¬ ∃ r, some false = some r ∧ r = false ∧ q`. The body of the `∃` is in the
vocabulary of `grind`, so E-matching instantiates `r := false` from the ground term `some false`,
and `h` yields `¬ q`.
-/

namespace Lean.Order

/-! ## Pointwise operations on function lattices -/

attribute [simp, grind norm] meet_apply join_apply iSup_apply iInf_apply top_apply bot_apply
  CompleteLattice.ofProp_apply himp_apply

/-! ## Components of pairs -/

attribute [simp, grind norm] Prod.fst_meet Prod.snd_meet Prod.fst_join Prod.snd_join
  Prod.fst_iSup Prod.snd_iSup Prod.fst_iInf Prod.snd_iInf Prod.fst_top Prod.snd_top
  Prod.fst_bot Prod.snd_bot Prod.fst_ofProp Prod.snd_ofProp
  Prod.fst_himp Prod.snd_himp

/-! ## The carrier `Prop` -/

attribute [simp, grind norm] CompleteLattice.ofProp_prop_eq meet_prop_eq_and join_prop_eq_or
  iSup_prop_eq_exists iInf_prop_eq_forall top_prop_eq bot_prop_eq himp_prop_eq_imp le_prop_eq_imp

/-! ## `⌜·⌝` as a homomorphism -/

attribute [simp, grind norm] CompleteLattice.ofProp_true CompleteLattice.ofProp_false
  CompleteLattice.ofProp_meet_ofProp CompleteLattice.ofProp_join_ofProp CompleteLattice.iSup_ofProp
  CompleteLattice.iInf_ofProp CompleteLattice.ofProp_himp_ofProp

/-! ## Elimination of `⊑` -/

attribute [simp, grind norm] le_pi_eq_forall CompleteLattice.ofProp_le_eq_imp
  CompleteLattice.meet_ofProp_le_eq_imp CompleteLattice.ofProp_meet_le_eq_imp le_top_iff bot_le_iff
  top_le_himp_iff join_le_iff le_meet_iff iSup_le_iff le_iInf_iff
  CompleteLattice.top_le_ofProp_iff

/-! ## Units and zeros -/

attribute [simp, grind norm] top_meet meet_top bot_meet meet_bot bot_join join_bot top_join
  join_top iSup_bot iInf_top

/-! ## Computation rules of predicate transformers -/

attribute [simp, grind norm] PredTrans.apply_pure PredTrans.apply_Pure_pure PredTrans.apply_bind
  PredTrans.apply_Bind_bind PredTrans.apply_Functor_map PredTrans.apply_Seq_seq
  PredTrans.apply_dite PredTrans.apply_ite PredTrans.apply_pushArg PredTrans.apply_popArg
  PredTrans.apply_liftArg PredTrans.apply_monadLift PredTrans.apply_pushExceptT
  PredTrans.apply_pushOptionT PredTrans.apply_throw PredTrans.apply_tryCatch
  PredTrans.apply_liftExcept PredTrans.apply_popExcept PredTrans.apply_get PredTrans.apply_set
  PredTrans.apply_modifyGet PredTrans.apply_read PredTrans.apply_MonadExcept_throw
  PredTrans.apply_MonadExcept_tryCatch PredTrans.apply_MonadState_get
  PredTrans.apply_MonadState_modifyGet PredTrans.apply_modify PredTrans.apply_modifyThe
  PredTrans.apply_MonadReader_read PredTrans.apply_frameClosure
  pushExcept_ok pushExcept_error pushOption_some pushOption_none
  FrameOp.pointwise_apply FrameOp.prod_fst FrameOp.prod_snd FrameOp.ignore_apply

end Lean.Order

end -- public section
