/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core
public import Init.Classical
public import Init.Control.Ensures
public import Init.Control.Lawful.MonadAttach

/-!
# `whileM`

`whileM f a` iterates `f : α → m (α ⊕ β)`, recursing on `.inl` and terminating on
`.inr`. `whileM_eq` exposes the body only at points witnessed accessible by
`whileM.IsPlausibleStep`.
-/

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- The body of `whileM`: run `f a`, recurse via `recur` on `.inl`, return on `.inr`. -/
@[inline] public abbrev whileM.body (f : α → m (α ⊕ β)) (recur : α → m β) (a : α) : m β := do
  match ← f a with
  | .inl a' => recur a'
  | .inr a' => pure a'

/-- `a' ≺ a` iff `f a` may return `.inl a'`. -/
public abbrev whileM.IsPlausibleStep (f : α → m (α ⊕ β)) : α → α → Prop :=
  fun a' a => Internal.MayReturn (f a) (.inl a')

/-- Pinning predicate for `whileM.impl`: trivial unless we have both an `Acc` and
an attach for `m`, in which case `v` is pinned to the value computed by `Acc`-induction. -/
noncomputable abbrev whileM.Pred (f : α → m (α ⊕ β)) (a : α) : m β → Prop :=
  open scoped Classical in
  if h : Acc (whileM.IsPlausibleStep f) a ∧ Exists Internal.IsAttach then
    fun v => v = h.1.recOn (motive := fun _ _ => m β) (fun x _ ih => do
      let ⟨s, hp⟩ ← h.2.choose (f x)
      match s, hp with
      | .inl x', hp => ih x' hp
      | .inr b, _ => pure b)
  else
    fun _ => True

noncomputable instance [Nonempty β] {f : α → m (α ⊕ β)} {a : α} :
    Nonempty (Subtype (whileM.Pred f a)) :=
  open scoped Classical in
  if h : Acc (whileM.IsPlausibleStep f) a ∧ Exists Internal.IsAttach then
    ⟨⟨h.1.recOn (motive := fun x _ => m β) (fun x _ ih => do
        let ⟨s, hp⟩ ← h.2.choose (f x)
        match s, hp with
        | .inl x', hp => ih x' hp
        | .inr b, _ => pure b),
      by simp only [whileM.Pred, dif_pos h]⟩⟩
  else
    ⟨⟨pure (Classical.choice inferInstance), by simp only [whileM.Pred, dif_neg h]⟩⟩

/-- Computational core of `whileM`: returns the loop value paired with its
`whileM.Pred` proof. -/
@[specialize] partial def whileM.impl [Nonempty β]
    (f : α → m (α ⊕ β)) (a : α) :
    Subtype (whileM.Pred f a) :=
  ⟨whileM.body f (whileM.impl f · |>.val) a, by
    simp only [whileM.Pred]
    split <;> rename_i h
    · suffices key : ∀ x (h_x : Acc (whileM.IsPlausibleStep f) x),
          whileM.body f (whileM.impl f · |>.val) x =
          h_x.recOn (motive := fun _ _ => m β) (fun x _ ih => do
            let ⟨s, hp⟩ ← h.2.choose (f x)
            match s, hp with
            | .inl x', hp => ih x' hp
            | .inr b, _ => pure b) from key a h.1
      intro x h_x
      induction h_x with
      | intro x next ih =>
        simp only [whileM.body]
        rw [← ((h.2.choose_spec.erases (f x)).bind_eq)]
        congr
        funext ⟨s, hp⟩
        cases s with
        | inr b => rfl
        | inl x' =>
          show (whileM.impl f x').val = _
          have h_x' : Acc (whileM.IsPlausibleStep f) x' ∧ _ := ⟨next x' hp, h.2⟩
          have hp_x' := (whileM.impl f x').property
          simp only [whileM.Pred, dif_pos h_x'] at hp_x'
          rw [hp_x']
    · exact True.intro⟩

/-- `whileM f a` iterates `f` at `a`, recursing on `.inl` and terminating on `.inr`. -/
@[inline] public def whileM [Nonempty β] (f : α → m (α ⊕ β)) (a : α) : m β :=
  (whileM.impl f a).val

/-- Under `Acc (whileM.IsPlausibleStep f) a`, `whileM f a` unfolds to one step. -/
-- We only need `MonadAttach` here for the `attach` function; lawfulness gives us that it
-- satisfies `Internal.IsAttach` (cf. `Internal.IsAttach.of_attach`). We could consider adding a
-- separate `HasAttach` type class for this in the future, but decided against it for now to avoid
-- introducing yet another type class for much the same purpose.
public theorem whileM_eq [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] [Nonempty β]
    {f : α → m (α ⊕ β)} (a : α) (h : Acc (whileM.IsPlausibleStep f) a) :
    whileM f a = whileM.body f (whileM f) a := by
  have hExAttach : Exists (Internal.IsAttach (m := m)) := by
    refine ⟨fun _ x =>
      (fun ⟨s, hCR⟩ => ⟨s, Internal.MayReturn.of_canReturn hCR⟩) <$> MonadAttach.attach x, ?_⟩
    refine ⟨fun {_} x => ⟨fun {β'} k => ?_⟩⟩
    rw [bind_map_left]
    exact Internal.ErasesTo.of_attach.bind_eq k
  have hGate : Acc (whileM.IsPlausibleStep f) a ∧ Exists Internal.IsAttach :=
    ⟨h, hExAttach⟩
  have hp_a := (whileM.impl f a).property
  simp only [whileM.Pred, dif_pos hGate] at hp_a
  show (whileM.impl f a).val = _
  rw [hp_a]
  suffices key : ∀ x (h_x : Acc (whileM.IsPlausibleStep f) x),
      whileM.body f (whileM.impl f · |>.val) x =
      h_x.recOn (motive := fun _ _ => m β) (fun x _ ih => do
        let ⟨s, hp⟩ ← hGate.2.choose (f x)
        match s, hp with
        | .inl x', hp => ih x' hp
        | .inr b, _ => pure b) from (key a hGate.1).symm
  intro x h_x
  induction h_x with
  | intro x next ih =>
    simp only [whileM.body]
    rw [← ((hGate.2.choose_spec.erases (f x)).bind_eq)]
    apply bind_congr
    intro ⟨s, hp⟩
    cases s with
    | inr b => rfl
    | inl x' =>
      show (whileM.impl f x').val = _
      have h_x' : Acc (whileM.IsPlausibleStep f) x' ∧
          Exists Internal.IsAttach :=
        ⟨next x' hp, hGate.2⟩
      have hp_x' := (whileM.impl f x').property
      simp only [whileM.Pred, dif_pos h_x'] at hp_x'
      rw [hp_x']

namespace Lean

/-!
# ForIn instance for `repeat`/`while` syntax

This section provides a `ForIn` instance for `Loop`, which is implemented via `whileM`.
This `ForIn` instance is used to implement `repeat`/`while` syntax.
-/

/-- The `Loop` type backing `repeat`/`while`. Its `ForIn` instance is `Loop.forIn`. -/
public structure Loop

/-- Iterate `f` until it returns `.done`, threading the accumulator through `.yield`. -/
@[inline, expose] public protected def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m]
    (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  haveI : Nonempty β := ⟨init⟩
  whileM (fun b => do
    match ← f () b with
    | .done b'  => pure (.inr b')
    | .yield b' => pure (.inl b')) init

public instance [Monad m] : ForIn m Loop Unit where
  forIn := Loop.forIn

end Lean
