import Std

/-!
# `extrinsicRepeat`: a classically-defined `repeat`/`while` loop combinator

`extrinsicRepeat f a` iterates `f : α → m (ForInStep α)` at `a`. Its definition only requires
`[Monad m]` — same obligations as `Loop.forIn`. Termination evidence is *extrinsic*: the
combinator is opaque by default and is only logically usable for proofs once a fixpoint is
established. Operationally, `@[implemented_by opaqueRepeat]` provides the runtime impl.

The classical condition `∃ g, IsFix f g ∧ Total f a` gates the dif: existence of any global
fixpoint of `repeatF f` *plus* totality (all fixpoints agree at `a`). When both hold, the
classical `h.choose a` is the well-defined loop value.

`MonadAttach` + lawfulness appear only in the *termination* and *Spec* sections, never in
`extrinsicRepeat`'s own type.

## Structure
- **Definition** — `repeatF`, `opaqueRepeat`, `IsFix`, `Total`, `extrinsicRepeat`, and the
  private `extrinsicRepeat_eq_fix` (the only way to "look inside" the classical choice).
- **Termination** — `IsPlausibleStep`, `IsLoopVariant`, and the public unfolding API
  `IsLoopVariant.extrinsicRepeat_unfold`. Internals (`bound_widen`, `hasFix`) are `private`.
- **Spec** — `IsLoopVariant.of_wp_measure` (WPAdequacy bridge) and `Spec.extrinsicRepeat`
  (the `@[spec]` theorem for `mvcgen` integration).
- **Sqrt example** — end-to-end `sqrt_correct` proof to demonstrate the full pipeline.
-/

section Definition

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- One-step unfolding of the loop body: run `f a`, return on `done`, recurse via `cont`
on `yield`. Used to phrase the fixpoint equation `g = repeatF f g` for any candidate `g`. -/
@[inline] def repeatF (f : α → m (ForInStep α)) (cont : α → m α) (a : α) : m α := do
  match ← f a with
  | .done a' => pure a'
  | .yield a' => cont a'

/-- `IsFix f g` says `g` is a (global) function fixpoint of `repeatF f`: `g = repeatF f g`. -/
def IsFix (f : α → m (ForInStep α)) (g : α → m α) : Prop :=
  g = repeatF f g

/-- `Total f a` says all fixpoints of `repeatF f` agree at `a`. -/
def Total (f : α → m (ForInStep α)) (a : α) : Prop :=
  ∀ g₁ g₂ : α → m α, IsFix f g₁ → IsFix f g₂ → g₁ a = g₂ a

/-- INTERNAL. Predicate pinning the loop value at `a` to `h.choose a` when a global
fixpoint of `repeatF f` exists; otherwise vacuous. -/
noncomputable def PredRepeat (f : α → m (ForInStep α)) : α → m α → Prop :=
  open scoped Classical in
  if h : ∃ g, IsFix f g then (h.choose · = ·) else (fun _ _ => True)

instance [Nonempty (m α)] {f : α → m (ForInStep α)} {a : α} :
    Nonempty (Subtype (PredRepeat f a)) := by
  by_cases h : ∃ g, IsFix f g
  · exact ⟨⟨h.choose a, by simp [PredRepeat, h]⟩⟩
  · exact ⟨⟨Classical.choice inferInstance, by simp [PredRepeat, h]⟩⟩

/-- INTERNAL. Computational core: at each `a`, returns the loop value packaged with the
predicate `PredRepeat f a` that pins it to the classical fixpoint when one exists.
Defined as a `partial def` so it computes operationally; the predicate carries the
logical content needed to prove unfolding. -/
partial def extrinsicRepeat' [Nonempty (m α)] (f : α → m (ForInStep α)) (a : α) :
    Subtype (PredRepeat f a) :=
  ⟨repeatF f (extrinsicRepeat' f · |>.val) a, by
    simp only [PredRepeat]
    split <;> rename_i h
    · simp
      have h' x := (extrinsicRepeat' f x).property
      simp [PredRepeat, h] at h'
      simp [← h']
      have := h.choose_spec
      rw [← this]
    · simp
    done⟩

/-- `extrinsicRepeat f a` iterates `f` at `a`. Same obligations as `Loop.forIn` (just
`[Monad m]`); computable without `@[implemented_by]` via the `PredRepeat`/`extrinsicRepeat'`
machinery above. -/
def extrinsicRepeat (f : α → m (ForInStep α)) (a : α) : m α :=
  haveI : Nonempty (m α) := ⟨pure a⟩
  (extrinsicRepeat' f a).val

/-- INTERNAL. Given any global fixpoint witness, `extrinsicRepeat f` *is* a fixpoint of
`repeatF f`. Don't use directly — go through `IsLoopVariant.extrinsicRepeat_unfold`. -/
private theorem extrinsicRepeat_eq_fix {f : α → m (ForInStep α)}
    (g : α → m α) (hfix : IsFix f g) :
    extrinsicRepeat f = repeatF f (extrinsicRepeat f) := by
  have h : ∃ g, IsFix f g := ⟨g, hfix⟩
  ext a
  haveI : Nonempty (m α) := ⟨pure a⟩
  show (extrinsicRepeat' f a).val = repeatF f (fun b => (extrinsicRepeat' f b).val) a
  have h' x := (extrinsicRepeat' f x).property
  simp [PredRepeat, h] at h'
  simp [← h']
  exact congrFun h.choose_spec a

end Definition

section Termination

variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadAttach m]

/-- Step relation: `a' ≺ a` iff `f a` can yield `a'`. -/
def IsPlausibleStep (f : α → m (ForInStep α)) : α → α → Prop :=
  fun a' a => MonadAttach.CanReturn (f a) (ForInStep.yield a')

/-- A user-supplied variant: every plausible yield of `f` strictly decreases `μ`. -/
def IsLoopVariant (μ : α → Nat) (f : α → m (ForInStep α)) : Prop :=
  ∀ a a', IsPlausibleStep f a' a → μ a' < μ a

omit [Monad m] in
/-- A valid variant gives accessibility of every point. -/
theorem IsLoopVariant.acc {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) (a : α) : Acc (IsPlausibleStep f) a :=
  Subrelation.accessible (fun h => hvar _ _ h) (InvImage.accessible μ (Nat.lt_wfRel.wf.apply (μ a)))

variable [LawfulMonad m] [WeaklyLawfulMonadAttach m]

/-- INTERNAL. Bind congruence using `MonadAttach.CanReturn` to supply the pointwise hypothesis. -/
private theorem bind_congr_canReturn {x : m α} {k1 k2 : α → m β}
    (h : ∀ a, MonadAttach.CanReturn x a → k1 a = k2 a) : x >>= k1 = x >>= k2 := by
  rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := x) (f := k1),
      ← WeaklyLawfulMonadAttach.attach_bind_val (x := x) (f := k2)]
  exact bind_congr fun ⟨a, ha⟩ => h a ha

/--
INTERNAL. Under a variant, widening the iteration count past `μ a + 1` doesn't change the value:
for all `N ≥ μ a + 1`, `Nat.repeat N pure a = Nat.repeat (μ a + 1) pure a`.
-/
private theorem IsLoopVariant.bound_widen {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) :
    ∀ N a, μ a + 1 ≤ N →
      Nat.repeat (repeatF f) N pure a = Nat.repeat (repeatF f) (μ a + 1) pure a := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro a hmu
    match N, hmu with
    | N + 1, hmu =>
      rcases Nat.lt_or_eq_of_le hmu with hlt | heq
      · show repeatF f (Nat.repeat (repeatF f) N pure) a =
             repeatF f (Nat.repeat (repeatF f) (μ a) pure) a
        simp only [repeatF]
        apply bind_congr_canReturn
        intro r hr
        cases r with
        | done b => rfl
        | yield a' =>
          have hlta : μ a' < μ a := hvar a a' hr
          show Nat.repeat (repeatF f) N pure a' = Nat.repeat (repeatF f) (μ a) pure a'
          rw [ih N (Nat.lt_succ_self _) a' (by omega),
              ih (μ a) (by omega) a' (by omega)]
      · rw [← heq]

/--
Under a variant, `a` is total: any two fixpoints of `repeatF f` agree at `a`. Proved by
strong induction on `μ a`, using `bind_congr_canReturn` pointwise on yields.
-/
theorem IsLoopVariant.total {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) (a : α) : Total f a := by
  intro g₁ g₂ h₁ h₂
  suffices ∀ k, ∀ a, μ a = k → g₁ a = g₂ a by
    exact this (μ a) a rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro a hka
    rw [congrFun h₁ a, congrFun h₂ a]
    simp only [repeatF]
    apply bind_congr_canReturn
    intro r hr
    cases r with
    | done b => rfl
    | yield a' =>
      have hlt : μ a' < k := hka ▸ hvar a a' hr
      exact ih (μ a') hlt a' rfl

/--
INTERNAL. Under a variant, the iterate function `g a := Nat.repeat (μ a + 1) pure a` is a
global fixpoint of `repeatF f`.
-/
private theorem IsLoopVariant.hasFix {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) : ∃ g, IsFix f g := by
  refine ⟨fun a => Nat.repeat (repeatF f) (μ a + 1) pure a, funext fun b => ?_⟩
  show repeatF f (Nat.repeat (repeatF f) (μ b) pure) b =
       repeatF f (fun a => Nat.repeat (repeatF f) (μ a + 1) pure a) b
  simp only [repeatF]
  apply bind_congr_canReturn
  intro r hr
  cases r with
  | done c => rfl
  | yield b' => exact hvar.bound_widen (μ b) b' (hvar b b' hr)

/--
**Public unfolding API.** Under a variant, `extrinsicRepeat f a` unfolds to one step of the
loop body. This is the *only* way downstream code should unfold `extrinsicRepeat` — the
classical internals (`extrinsicRepeat_eq_fix`, `hasFix`, `bound_widen`) are `private`.
-/
theorem IsLoopVariant.extrinsicRepeat_unfold {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) (a : α) :
    extrinsicRepeat f a = repeatF f (extrinsicRepeat f) a := by
  obtain ⟨g, hfix⟩ := hvar.hasFix
  exact congrFun (extrinsicRepeat_eq_fix g hfix) a

/--
INTERNAL. `extrinsicRepeat f a` unfolded with the `MonadAttach.attach` structure exposed,
so downstream `mvcgen` proofs can see `CanReturn (f a) r` when reasoning about yielded values.
-/
private theorem IsLoopVariant.extrinsicRepeat_unfold_attach {μ : α → Nat}
    {f : α → m (ForInStep α)} (hvar : IsLoopVariant μ f) (a : α) :
    extrinsicRepeat f a = (MonadAttach.attach (f a) >>= fun x => match x.val with
      | .done b => pure b
      | .yield b => extrinsicRepeat f b) := by
  rw [hvar.extrinsicRepeat_unfold a]
  simp only [repeatF]
  rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := f a)]

end Termination

section Spec

open Std.Do

variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [WPMonad m ps]

omit [LawfulMonad m] [WeaklyLawfulMonadAttach m] [WPMonad m ps] in
/-- Derive `IsLoopVariant` from a WP-based decrease proof (via `WPAdequacy`). -/
theorem IsLoopVariant.of_wp_measure [WPAdequacy m ps]
    (μ : β → Nat) (f : β → m (ForInStep β))
    (h : ∀ b, ⦃⌜True⌝⦄ f b ⦃⇓ step => ⌜∀ b', step = .yield b' → μ b' < μ b⌝⦄) :
    IsLoopVariant μ f := by
  intro a a' hr
  have h' : ⊢ₛ wp⟦f a⟧ (⇓? step => ⌜∀ b', step = .yield b' → μ b' < μ a⌝) := by
    apply SPred.entails.trans (Triple.iff.mp (h a))
    apply (wp (f a)).mono
    simp [PostCond.entails]
  exact WPAdequacy.adequate (m := m) (ps := ps) (x := f a)
    (P := fun step => ∀ b', step = .yield b' → μ b' < μ a) h' (.yield a') hr a' rfl

/--
**Public `@[spec]` theorem for `extrinsicRepeat`.** Under a variant `μ` and a step-preserving
invariant, the whole loop satisfies the invariant.
-/
@[spec]
theorem Spec.extrinsicRepeat
    {init : β} {f : β → m (ForInStep β)}
    (μ : RepeatVariant β)
    (inv : RepeatInvariant β ps)
    (hvar : IsLoopVariant μ f)
    (step : ∀ b, Triple (f b) (inv.1 (.repeat b))
        (fun r => match r with
          | .yield b' => inv.1 (.repeat b')
          | .done b' => inv.1 (.done b'), inv.2)) :
    Triple (extrinsicRepeat f init) (inv.1 (.repeat init))
        (fun b => inv.1 (.done b), inv.2) := by
  induction hvar.acc init with
  | intro a _ ih =>
    rw [hvar.extrinsicRepeat_unfold_attach a]
    mvcgen [step, ih]
    rename_i stp
    apply SPred.forall_intro
    intro _
    cases stp <;> mvcgen [ih]

end Spec

section SqrtExample

open Std.Do

/-- `sqrt n` computes the integer square root of `n` using `extrinsicRepeat`. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let res ← extrinsicRepeat
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
      grind
    · cases hr
  | vc5.isFalse.post.success res h =>
    have : res - 1 < res := by grind
    grind

#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 100) == 10

end SqrtExample

