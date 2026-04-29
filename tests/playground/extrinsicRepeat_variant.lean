import Std

set_option mvcgen.warning false

/-!
# `Repeat.loop`: a classically-defined `repeat`/`while` loop combinator

`Repeat.loop f a` iterates `f : α → m (ForInStep α)` at `a`. Its definition only requires
`[Monad m]` — same obligations as `Loop.forIn`. Termination evidence is *extrinsic*: the
combinator is opaque by default and is only logically usable for proofs once a fixpoint is
established. Operationally, `@[implemented_by opaqueRepeat]` provides the runtime impl.

The classical condition `∃ g, g = Repeat.body f g` gates the dif: existence of any global
fixpoint of `Repeat.body f`. When it holds, the classical `h.choose a` is the loop value.

`MonadAttach` + lawfulness appear only in the *termination* and *Spec* sections, never in
`Repeat.loop`'s own type.

## Structure
- **Definition** — `Repeat.body`, `RepeatPred`, `Repeat.loop'`, `Repeat.loop`, and the
  private `extrinsicRepeat_eq_fix` (the only way to "look inside" the classical choice).
- **Termination** — `IsPlausibleStep`, `IsRepeatVariant`, and the public unfolding API
  `IsRepeatVariant.extrinsicRepeat_unfold`. Internals (`bound_widen`, `hasFix`) are `private`.
- **Spec** — `IsRepeatVariant.of_wp_measure` (WPAdequacy bridge) and `Spec.Repeat.loop`
  (the `@[spec]` theorem for `mvcgen` integration).
- **Sqrt example** — end-to-end `sqrt_correct` proof to demonstrate the full pipeline.
-/

section Definition

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- One-step unfolding of the loop body: run `f a`, return on `done`, recurse via `cont`
on `yield`. Used to phrase the fixpoint equation `g = Repeat.body f g` for any candidate `g`. -/
@[inline] abbrev Repeat.body (f : α → m (ForInStep α)) (cont : α → m α) (a : α) : m α := do
  match ← f a with
  | .done a' => pure a'
  | .yield a' => cont a'

private def RepeatPred (f : α → m (ForInStep α)) (a : α) : m α → Prop :=
  open scoped Classical in
  if h : ∃ g, g = Repeat.body f g then (h.choose a = ·) else (fun _ => True)

private instance {f : α → m (ForInStep α)} {a : α} :
    Nonempty (Subtype (RepeatPred f a)) := by
  by_cases h : ∃ g, g = Repeat.body f g
  · exact ⟨⟨h.choose a, by simp [RepeatPred, h]⟩⟩
  · exact ⟨⟨pure a, by simp [RepeatPred, h]⟩⟩

/-- INTERNAL. Computational core: at each `a`, returns the loop value packaged with the
predicate `RepeatPred f a` that pins it to the classical fixpoint when one exists.
Defined as a `partial def` so it computes operationally; the predicate carries the
logical content needed to prove unfolding. -/
@[specialize] private partial def Repeat.loop.impl (f : α → m (ForInStep α)) (a : α) :
    Subtype (RepeatPred f a) :=
  ⟨Repeat.body f (Repeat.loop.impl f · |>.val) a, by
    simp only [RepeatPred]
    split <;> rename_i h
    · simp
      have h' x := (Repeat.loop.impl f x).property
      simp [RepeatPred, h] at h'
      simp [← h']
      have := h.choose_spec
      rw [← this]
    · simp
    done⟩

/-- `Repeat.loop f a` iterates `f` at `a`. Same obligations as `Loop.forIn` (just
`[Monad m]`); computable without `@[implemented_by]` via the `RepeatPred`/`Repeat.loop.impl`
machinery above. -/
@[inline] def Repeat.loop (f : α → m (ForInStep α)) (a : α) : m α :=
  (Repeat.loop.impl f a).val

/-- INTERNAL. Given any global fixpoint witness, `Repeat.loop f` *is* a fixpoint of
`Repeat.body f`. Don't use directly — go through `IsRepeatVariant.extrinsicRepeat_unfold`. -/
private theorem extrinsicRepeat_eq_fix {f : α → m (ForInStep α)}
    (g : α → m α) (hfix : g = Repeat.body f g) :
    Repeat.loop f = Repeat.body f (Repeat.loop f) := by
  have h : ∃ g, g = Repeat.body f g := ⟨g, hfix⟩
  ext a
  haveI : Nonempty (m α) := ⟨pure a⟩
  show (Repeat.loop.impl f a).val = Repeat.body f (fun b => (Repeat.loop.impl f b).val) a
  have h' x := (Repeat.loop.impl f x).property
  simp [RepeatPred, h] at h'
  simp [← h']
  exact congrFun h.choose_spec a

end Definition

section Termination

variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadAttach m]

/-- Step relation: `a' ≺ a` iff `f a` can yield `a'`. -/
private def IsPlausibleStep (f : α → m (ForInStep α)) : α → α → Prop :=
  fun a' a => MonadAttach.CanReturn (f a) (ForInStep.yield a')

/-- A user-supplied variant: every plausible yield of `f` strictly decreases `μ` according
to a well-founded relation on `γ`. -/
def IsRepeatVariant {γ : Sort _} [WellFoundedRelation γ]
    (μ : α → γ) (f : α → m (ForInStep α)) : Prop :=
  ∀ a a', IsPlausibleStep f a' a → WellFoundedRelation.rel (μ a') (μ a)

omit [Monad m] in
/-- Under a variant, every `a` is accessible. -/
private theorem IsRepeatVariant.acc {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (ForInStep α)}
    (hvar : IsRepeatVariant μ f) (a : α) : Acc (IsPlausibleStep f) a :=
  Subrelation.accessible (r := InvImage WellFoundedRelation.rel μ)
    (fun {a' b} h => hvar b a' h)
    (InvImage.accessible μ (WellFoundedRelation.wf.apply (μ a)))

variable [LawfulMonad m] [WeaklyLawfulMonadAttach m]

@[inline] private def repeatFAttach (f : α → m (ForInStep α)) (a : α)
    (cont : (a' : α) → MonadAttach.CanReturn (f a) (.yield a') → m α) : m α := do
  match ← MonadAttach.attach (f a) with
  | ⟨.done a', _⟩ => pure a'
  | ⟨.yield a', h⟩ => cont a' h

/--
Under a variant, `WellFounded.fix` of `repeatFAttach` is a global fixpoint of
`Repeat.body f`. Works for any `WellFoundedRelation γ`, not just `Nat`.
-/
private theorem IsRepeatVariant.hasFix {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (ForInStep α)}
    (hvar : IsRepeatVariant μ f) : ∃ g, g = Repeat.body f g := by
  let hwf : WellFounded (IsPlausibleStep f) :=
    Subrelation.wf (fun h => hvar _ _ h) (InvImage.wf μ WellFoundedRelation.wf)
  refine ⟨WellFounded.fix hwf (repeatFAttach f), funext fun a => ?_⟩
  rw [WellFounded.fix_eq]
  simp only [repeatFAttach, Repeat.body]
  rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := f a)]
  apply bind_congr
  rintro ⟨r, h⟩
  cases r <;> rfl

/--
**Public unfolding API.** Under a variant, `Repeat.loop f a` unfolds to one step of the
loop body. This is the *only* way downstream code should unfold `Repeat.loop` — the
classical internals (`extrinsicRepeat_eq_fix`, `hasFix`) are `private`.
-/
theorem IsRepeatVariant.extrinsicRepeat_unfold {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (ForInStep α)}
    (hvar : IsRepeatVariant μ f) (a : α) :
    Repeat.loop f a = Repeat.body f (Repeat.loop f) a := by
  obtain ⟨g, hfix⟩ := hvar.hasFix
  exact congrFun (extrinsicRepeat_eq_fix g hfix) a

end Termination

section Spec

open Std.Do

variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [WPMonad m ps]

omit [LawfulMonad m] [WeaklyLawfulMonadAttach m] [WPMonad m ps] in
/-- Derive `IsRepeatVariant` from a WP-based decrease proof (via `WPAdequacy`). -/
theorem IsRepeatVariant.of_wp_measure [WPAdequacy m ps]
    (μ : β → Nat) (f : β → m (ForInStep β))
    (h : ∀ b, ⦃⌜True⌝⦄ f b ⦃⇓ step => ⌜∀ b', step = .yield b' → μ b' < μ b⌝⦄) :
    IsRepeatVariant μ f := by
  intro a a' hr
  have h' : ⊢ₛ wp⟦f a⟧ (⇓? step => ⌜∀ b', step = .yield b' → μ b' < μ a⌝) := by
    apply SPred.entails.trans (Triple.iff.mp (h a))
    apply (wp (f a)).mono
    simp [PostCond.entails]
  exact WPAdequacy.adequate (m := m) (ps := ps) (x := f a)
    (P := fun step => ∀ b', step = .yield b' → μ b' < μ a) h' (.yield a') hr a' rfl

/--
**Public `@[spec]` theorem for `Repeat.loop`.** Under a variant `μ` and a step-preserving
invariant, the whole loop satisfies the invariant.
-/
@[spec]
theorem Spec.Repeat.loop
    {init : β} {f : β → m (ForInStep β)}
    (μ : RepeatVariant β)
    (inv : RepeatInvariant β ps)
    (hvar : IsRepeatVariant μ f)
    (step : ∀ b, Triple (f b) (inv.1 (.repeat b))
        (fun r => match r with
          | .yield b' => inv.1 (.repeat b')
          | .done b' => inv.1 (.done b'), inv.2)) :
    Triple (Repeat.loop f init) (inv.1 (.repeat init))
        (fun b => inv.1 (.done b), inv.2) := by
  induction hvar.acc init with
  | intro a _ ih =>
    rw [hvar.extrinsicRepeat_unfold a]
    simp only [Repeat.body]
    rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := f a)]
    mvcgen [step, ih]
    rename_i stp
    apply SPred.forall_intro
    intro _
    cases stp <;> mvcgen [ih]

end Spec

section SqrtExample

open Std.Do

/-- `sqrt n` computes the integer square root of `n` using `Repeat.loop`. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let res ← Repeat.loop
    (fun i => pure (if i * i ≤ n then .yield (i + 1) else .done i))
    0
  return res - 1

/-- The `sqrt` function returns the correct integer square root. -/
theorem sqrt_correct :
    ⦃⌜True⌝⦄ sqrt n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res + 1)⌝⦄ := by
  mvcgen [sqrt]
  invariants
  | inv1 => fun i => (n + 2) - i
  | inv2 => ⇓ cursor => match cursor with
    | .repeat i => ⌜∀ j, j < i → j * j ≤ n⌝
    | .done i => ⌜(∀ j, j < i → j * j ≤ n) ∧ n < i * i⌝
  with (try grind)
  | vc2.hvar =>
    intro a a' hr
    simp [IsPlausibleStep, MonadAttach.CanReturn, Id.run] at hr
    split at hr
    · cases hr
      rename_i h
      have : a ≤ n := Nat.le_trans (Nat.le_mul_self a) h
      simp_wf
      grind
    · cases hr
  | vc5.isFalse.post.success res h =>
    have : res - 1 < res := by grind
    grind

#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 100) == 10

end SqrtExample
