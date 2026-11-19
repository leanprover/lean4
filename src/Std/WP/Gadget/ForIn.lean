/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.BinderNameHint
public import Std.WP.Triple.SpecLemmas
public import Std.Internal.ForIn

/-!
# `forIn` loop-invariant gadgets

`forInPureWithInvariant` and `forInPureWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. Their `@[spec]` specifications
restate `Spec.forIn_list`/`Spec.forIn'_list` for every container with a `PureForIn` instance.

`forInLoopWithInvariant`, `forInLoopWithVariant` and `forInLoopWithInvariantAndVariant` do the same
for a `repeat` loop, one per set of annotations the loop states. Each restates `Spec.forIn_loop`,
leaving what the loop does not state to `vcgen` to infer.
-/

@[expose] public section

namespace Std.WP

open Lean.Order
open Std.Internal
open Assertion

universe u u₁ u₂ v w wₚ wₑ
variable {α : Type u₁} {β : Type u₂} {m : Type u₂ → Type v} {Pred : Type wₚ} {EPosts : Type wₑ}
variable [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]

/-! ## Gadgets -/

namespace Gadget

set_option linter.unusedVariables false in
/-- A `forIn` loop annotated with its loop invariant, which `vcgen` reads from the `inv` argument.
It is definitionally `forIn xs init f`, so the annotation is erased at runtime. The invariant
ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def forInPureWithInvariant {ρ : Type w} [ForIn m ρ α] (xs : ρ) (init : β)
    (f : α → β → m (ForInStep β)) (inv : Invariant α β Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A membership-aware `forIn'` loop annotated with its loop invariant, which `vcgen` reads from the
`inv` argument. It is definitionally `forIn' xs init f`, so the annotation is erased at runtime. The
invariant ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def forInPureWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : Invariant α β Pred) : m β :=
  forIn' xs init f

end Gadget

open Gadget

/-! ## Specifications -/

@[spec]
theorem Spec.forInPureWithInvariant {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {eposts : EPosts}
    (step : ∀ pref cur suff (_h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint suff (inv pref) <|
          binderNameHint cur f <| binderNameHint b (inv pref (cur :: suff)) <|
          inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        eposts) :
    Triple
      (Gadget.forInPureWithInvariant xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => binderNameHint b (inv (ForIn.toList xs) []) <| inv (ForIn.toList xs) [] b)
      eposts := by
  unfold Gadget.forInPureWithInvariant
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInPureWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {eposts : EPosts}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) b)
        (binderNameHint pref inv <| binderNameHint suff (inv pref) <|
          binderNameHint cur f <| binderNameHint b (inv pref (cur :: suff)) <|
          inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        eposts) :
    Triple
      (Gadget.forInPureWithInvariant' xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => binderNameHint b (inv (ForIn.toList xs) []) <| inv (ForIn.toList xs) [] b)
      eposts := by
  unfold Gadget.forInPureWithInvariant'
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list inv step

@[spec default+10]
theorem Spec.forInPureWithInvariant_earlyReturn {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α]
    {γ δ : Type u₂} {xs : ρ} {init : β}
    {f : α → Option γ × β → m (ForInStep (Option γ × β))}
    {kRet : Option γ × β → γ → m δ} {k : Option γ × β → m δ}
    {post : δ → Pred} {eposts : EPosts}
    (inv : List α → List α → Option γ × β → Pred)
    (step : ∀ pref cur suff (_h : ForIn.toList xs = pref ++ cur :: suff) b,
      ⦃ inv pref (cur :: suff) (none, b) ⦄ f cur (none, b)
      ⦃ fun r => match r with
          | .yield (none, b') => inv (pref ++ [cur]) suff (none, b')
          | .done (none, b') => inv (ForIn.toList xs) [] (none, b')
          | .done (some x, b') => wp (kRet (some x, b') x) post eposts
          | .yield (some _, _) => ⊥; eposts ⦄)
    (exit : ∀ b, ⦃ inv (ForIn.toList xs) [] (none, b) ⦄ k (none, b) ⦃ post; eposts ⦄) :
    ⦃ inv [] (ForIn.toList xs) (none, init) ⦄
    (Gadget.forInPureWithInvariant xs (none, init) f inv >>= fun s =>
      Break.runK.match_1 (fun _ => m δ) s.fst (fun x => kRet s x) (fun _ => k s))
    ⦃ post; eposts ⦄ :=
  Spec.forIn_pure_earlyReturn (fun pref suff b => inv pref suff (none, b)) step exit

@[spec default+10]
theorem Spec.forInPureWithInvariant'_earlyReturn {ρ : Type w} {d : Membership α ρ}
    [ForIn' m ρ α d] [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {γ δ : Type u₂} {xs : ρ} {init : β}
    {f : (a : α) → a ∈ xs → Option γ × β → m (ForInStep (Option γ × β))}
    {kRet : Option γ × β → γ → m δ} {k : Option γ × β → m δ}
    {post : δ → Pred} {eposts : EPosts}
    (inv : List α → List α → Option γ × β → Pred)
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      ⦃ inv pref (cur :: suff) (none, b) ⦄
      f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) (none, b)
      ⦃ fun r => match r with
          | .yield (none, b') => inv (pref ++ [cur]) suff (none, b')
          | .done (none, b') => inv (ForIn.toList xs) [] (none, b')
          | .done (some x, b') => wp (kRet (some x, b') x) post eposts
          | .yield (some _, _) => ⊥; eposts ⦄)
    (exit : ∀ b, ⦃ inv (ForIn.toList xs) [] (none, b) ⦄ k (none, b) ⦃ post; eposts ⦄) :
    ⦃ inv [] (ForIn.toList xs) (none, init) ⦄
    (Gadget.forInPureWithInvariant' xs (none, init) f inv >>= fun s =>
      Break.runK.match_1 (fun _ => m δ) s.fst (fun x => kRet s x) (fun _ => k s))
    ⦃ post; eposts ⦄ :=
  Spec.forIn'_pure_earlyReturn (fun pref suff b => inv pref suff (none, b)) step exit


section Loop

universe uₚ uₑ uq uγ uf

namespace Gadget

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the loop invariant that `vcgen` reads from the `inv` argument.
It is definitionally `forIn l init f`, so the annotation is erased at runtime. The invariant takes
the loop's `exit` flag, `false` while the loop iterates and `true` once it is done. -/
@[inline] def forInLoopWithInvariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : WhileInvariant β Pred) : m β :=
  forIn l init f

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the termination measure that `vcgen` reads from the `var`
argument. It is definitionally `forIn l init f`, so the annotation is erased at runtime. The measure
is the function a `Variant` is built from, so that the assertion language it evaluates in is
the one the specification is applied at. -/
@[inline] def forInLoopWithVariant {β : Type u} {m : Type u → Type v} {Fun : Type}
    [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (var : β → Fun) : m β :=
  forIn l init f

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the loop invariant and the termination measure that `vcgen` reads
from the `inv` and `var` arguments. It is definitionally `forIn l init f`, so the annotations are
erased at runtime. The invariant takes the loop's `exit` flag, `false` while the loop iterates and
`true` once it is done. The measure is the function a `Variant` is built from, so that the
assertion language it evaluates in is the one the specification is applied at. -/
@[inline] def forInLoopWithInvariantAndVariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    {Fun : Type} [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : WhileInvariant β Pred) (var : β → Fun) : m β :=
  forIn l init f

end Gadget

variable {β : Type u} {m : Type u → Type v} {Pred : Type uₚ} {EPosts : Type uₑ}
variable [Monad m] [Lean.Order.MonadTail m] [Assertion Pred] [Assertion EPosts]
  [WPMonad m Pred EPosts]

@[spec]
theorem Spec.forInLoopWithInvariantAndVariant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : Bool → β → Pred)
    (einv : EPosts)
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <|
          (Variant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (Gadget.forInLoopWithInvariantAndVariant l init f (WhileInvariant.mk inv) measure)
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold Gadget.forInLoopWithInvariantAndVariant
  exact Spec.forIn_loop (Variant.ofMeasure measure) inv einv step

@[spec]
theorem Spec.forInLoopWithInvariant
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : Variant β Pred)
    (inv : Bool → β → Pred)
    (einv : EPosts)
    (step : ∀ b (mb : measure.γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <| measure.EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (Gadget.forInLoopWithInvariant l init f (WhileInvariant.mk inv))
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold Gadget.forInLoopWithInvariant
  exact Spec.forIn_loop measure inv einv step

@[spec]
theorem Spec.forInLoopWithVariant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : WhileInvariant β Pred)
    (einv : EPosts)
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <|
          (Variant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (Gadget.forInLoopWithVariant l init f measure)
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold Gadget.forInLoopWithVariant
  exact Spec.forIn_loop (Variant.ofMeasure measure) inv einv step

@[spec default+10]
theorem Spec.forInLoopWithInvariantAndVariant_earlyReturn {Fun : Type} {γ : Type uγ'} {ω δ : Type u}
    {l : Lean.Loop} {init : β} {f : Unit → Option ω × β → m (ForInStep (Option ω × β))}
    {kRet : Option ω × β → ω → m δ} {k : Option ω × β → m δ} {post : δ → Pred}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : Option ω × β → Fun)
    (inv : Bool → Option ω × β → Pred)
    (einv : EPosts)
    (step : ∀ b (mb : γ),
      ⦃ (Variant.ofMeasure (Pred := Pred) measure).EvalsTo (none, b) mb ⊓ inv false (none, b) ⦄
      f () (none, b)
      ⦃ fun r => match r with
          | .yield (none, b') =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow (none, b') mb ⊓
              inv false (none, b')
          | .done (none, b') => inv true (none, b')
          | .done (some x, b') => wp (kRet (some x, b') x) post einv
          | .yield (some _, _) => ⊥; einv ⦄)
    (exit : ∀ b, ⦃ inv true (none, b) ⦄ k (none, b) ⦃ post; einv ⦄) :
    ⦃ inv false (none, init) ⦄
    (Gadget.forInLoopWithInvariantAndVariant l (none, init) f (WhileInvariant.mk inv) measure
      >>= fun s =>
      Break.runK.match_1 (fun _ => m δ) s.fst (fun x => kRet s x) (fun _ => k s))
    ⦃ post; einv ⦄ :=
  Spec.forIn_loop_earlyReturn (Variant.ofMeasure measure)
    (WhileInvariant.mk fun exit b => inv exit (none, b)) einv step exit

@[spec default+10]
theorem Spec.forInLoopWithInvariant_earlyReturn {ω δ : Type u}
    {l : Lean.Loop} {init : β} {f : Unit → Option ω × β → m (ForInStep (Option ω × β))}
    {kRet : Option ω × β → ω → m δ} {k : Option ω × β → m δ} {post : δ → Pred}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : Variant (Option ω × β) Pred)
    (inv : Bool → Option ω × β → Pred)
    (einv : EPosts)
    (step : ∀ b (mb : measure.γ),
      ⦃ measure.EvalsTo (none, b) mb ⊓ inv false (none, b) ⦄ f () (none, b)
      ⦃ fun r => match r with
          | .yield (none, b') => measure.EvalsBelow (none, b') mb ⊓ inv false (none, b')
          | .done (none, b') => inv true (none, b')
          | .done (some x, b') => wp (kRet (some x, b') x) post einv
          | .yield (some _, _) => ⊥; einv ⦄)
    (exit : ∀ b, ⦃ inv true (none, b) ⦄ k (none, b) ⦃ post; einv ⦄) :
    ⦃ inv false (none, init) ⦄
    (Gadget.forInLoopWithInvariant l (none, init) f (WhileInvariant.mk inv) >>= fun s =>
      Break.runK.match_1 (fun _ => m δ) s.fst (fun x => kRet s x) (fun _ => k s))
    ⦃ post; einv ⦄ :=
  Spec.forIn_loop_earlyReturn measure (WhileInvariant.mk fun exit b => inv exit (none, b)) einv
    step exit

@[spec default+10]
theorem Spec.forInLoopWithVariant_earlyReturn {Fun : Type} {γ : Type uγ'} {ω δ : Type u}
    {l : Lean.Loop} {init : β} {f : Unit → Option ω × β → m (ForInStep (Option ω × β))}
    {kRet : Option ω × β → ω → m δ} {k : Option ω × β → m δ} {post : δ → Pred}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : Option ω × β → Fun)
    (inv : WhileInvariant β Pred)
    (einv : EPosts)
    (step : ∀ b (mb : γ),
      ⦃ (Variant.ofMeasure (Pred := Pred) measure).EvalsTo (none, b) mb ⊓ inv false b ⦄
      f () (none, b)
      ⦃ fun r => match r with
          | .yield (none, b') =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow (none, b') mb ⊓ inv false b'
          | .done (none, b') => inv true b'
          | .done (some x, b') => wp (kRet (some x, b') x) post einv
          | .yield (some _, _) => ⊥; einv ⦄)
    (exit : ∀ b, ⦃ inv true b ⦄ k (none, b) ⦃ post; einv ⦄) :
    ⦃ inv false init ⦄
    (Gadget.forInLoopWithVariant l (none, init) f measure >>= fun s =>
      Break.runK.match_1 (fun _ => m δ) s.fst (fun x => kRet s x) (fun _ => k s))
    ⦃ post; einv ⦄ :=
  Spec.forIn_loop_earlyReturn (Variant.ofMeasure measure) inv einv step exit


end Loop

end Std.WP
