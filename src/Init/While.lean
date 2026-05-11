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

/-- The classical `Acc`-induction defining `whileM`, factored out so it can be referenced from
`whileM.Pred`, `whileM.impl`, and `whileM_eq` without duplicating the recursion. -/
private noncomputable def whileM.fix {β : Type u} (f : α → m (α ⊕ β))
    (hAttach : Exists (Internal.IsAttach (m := m))) {a : α}
    (h_a : Acc (whileM.IsPlausibleStep f) a) : m β :=
  h_a.recOn (motive := fun _ _ => m β) (fun x _ ih => do
    let ⟨s, hp⟩ ← hAttach.choose (f x)
    match s, hp with
    | .inl x', hp => ih x' hp
    | .inr b, _ => pure b)

/-- Pinning predicate for `whileM.impl`: trivial unless we have both an `Acc` and
an attach for `m`, in which case `v` is pinned to the value computed by `whileM.fix`. -/
private noncomputable abbrev whileM.Pred (f : α → m (α ⊕ β)) (a : α) (r : m β) : Prop :=
  open scoped Classical in
  if h : Acc (whileM.IsPlausibleStep f) a ∧ Exists Internal.IsAttach then
    r = whileM.fix f h.2 h.1
  else
    True

private noncomputable instance [Nonempty β] {f : α → m (α ⊕ β)} {a : α} :
    Nonempty (Subtype (whileM.Pred f a)) :=
  open scoped Classical in
  if h : Acc (whileM.IsPlausibleStep f) a ∧ Exists Internal.IsAttach then
    ⟨⟨whileM.fix f h.2 h.1, by simp only [whileM.Pred, dif_pos h]⟩⟩
  else
    ⟨⟨pure (Classical.choice inferInstance), by simp only [whileM.Pred, dif_neg h]⟩⟩

/-- The body of `whileM` at any `Subtype (whileM.Pred f ·)`-valued recursive call agrees with
`whileM.fix`, by `Acc` cases plus `Pred`-unfolding at the recursive step. -/
private theorem whileM.body_eq_fix
    (f : α → m (α ⊕ β)) (hAttach : Exists (Internal.IsAttach (m := m)))
    (g : (a : α) → Subtype (whileM.Pred f a))
    {x : α} (h_x : Acc (whileM.IsPlausibleStep f) x) :
    whileM.body f (g · |>.val) x = whileM.fix f hAttach h_x := by
  cases h_x with | intro x next =>
  simp only [whileM.body, whileM.fix]
  rw [← ((hAttach.choose_spec.erases (f x)).bind_eq)]
  apply bind_congr
  intro ⟨s, hp⟩
  cases s with
  | inr b => rfl
  | inl x' =>
    have hp_x' := (g x').property
    simp only [whileM.Pred,
      dif_pos (show Acc _ x' ∧ _ from ⟨next x' hp, hAttach⟩)] at hp_x'
    exact hp_x'

/-- Computational core of `whileM`: returns the loop value paired with its
`whileM.Pred` proof. -/
@[specialize] partial def whileM.impl [Nonempty β]
    (f : α → m (α ⊕ β)) (a : α) :
    Subtype (whileM.Pred f a) :=
  ⟨whileM.body f (whileM.impl f · |>.val) a, by
    simp only [whileM.Pred]
    split <;> rename_i h
    · exact whileM.body_eq_fix f h.2 (whileM.impl f) h.1
    · trivial⟩

/--
An erased version of `whileM.impl` that eta-expands better in the compiler.
Can be removed once `whileM.impl` optimizes to the same code.
-/
@[specialize] private partial def whileM.erased [Nonempty β] (f : α → m (α ⊕ β)) (a : α) : m β :=
  whileM.body f (whileM.erased f ·) a

/-- `whileM f a` iterates `f` at `a`, recursing on `.inl` and terminating on `.inr`. -/
@[inline, implemented_by whileM.erased] -- See comment above `whileM.erased`.
public def whileM [Nonempty β] (f : α → m (α ⊕ β)) (a : α) : m β :=
  (whileM.impl f a).val

/-- Under `Acc (whileM.IsPlausibleStep f) a`, `whileM f a` unfolds to one step. -/
-- We only need `MonadAttach` here for the `attach` function; lawfulness gives us that it
-- satisfies `Internal.IsAttach` (cf. `Internal.IsAttach.of_attach`). We could consider adding a
-- separate `HasAttach` type class for this in the future, but decided against it for now to avoid
-- introducing yet another type class for much the same purpose.
public theorem whileM_eq [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] [Nonempty β]
    {f : α → m (α ⊕ β)} (a : α) (h : Acc (whileM.IsPlausibleStep f) a) :
    whileM f a = whileM.body f (whileM f) a := by
  have hAttach : Exists (Internal.IsAttach (m := m)) := ⟨_, Internal.IsAttach.of_attach⟩
  have hp_a := (whileM.impl f a).property
  simp only [whileM.Pred, dif_pos (⟨h, hAttach⟩ : _ ∧ _)] at hp_a
  show (whileM.impl f a).val = _
  rw [hp_a]
  exact (whileM.body_eq_fix f hAttach (whileM.impl f) h).symm

namespace Lean

/-!
# `Loop` type backing `repeat`/`while`/`repeat ... until`

The parsers and elaborators for `repeat`, `while`, and `repeat ... until` live in
`Lean.Parser.Do` and `Lean.Elab.BuiltinDo.Repeat`. This module only provides the
`Loop` type (and `ForIn` instance) that those elaborators expand to.
-/

public structure Loop

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
