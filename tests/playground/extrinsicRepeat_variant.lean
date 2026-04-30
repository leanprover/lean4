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

/-- `MayReturnM x a` says `a` is in the image of `x` — `x` cannot be lifted to a monadic value
in `{b // b ≠ a}`. Same role as `MonadAttach.CanReturn`, but is just a closed `Functor`-level
definition (no typeclass). -/
def MayReturnM {m : Type u → Type v} [Functor m] {α : Type u} (x : m α) (a : α) : Prop :=
  ¬ ∃ y : m {b : α // b ≠ a}, Subtype.val <$> y = x

/-- Discharge a postcondition from `MayReturnM`: if `x` lifts to `m {b // P b}`, then `P` holds
at every value `MayReturnM` says `x` may return. (Classical, via the singleton predicate.) -/
theorem MayReturnM.imp {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u}
    {x : m α} {P : α → Prop} (a : α) (hCR : MayReturnM x a)
    (y : m {b // P b}) (hy : Subtype.val <$> y = x) : P a := by
  refine Classical.byContradiction fun hPa => hCR ⟨?_, ?_⟩
  · exact (fun b => ⟨b.val, fun heq => hPa (heq ▸ b.property)⟩) <$> y
  · rw [← hy]; simp only [← LawfulMonad.bind_pure_comp, bind_assoc, pure_bind]

section Definition

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- One-step unfolding of the loop body: run `f a`, return on `done`, recurse via `cont`
on `yield`. Used to phrase the fixpoint equation `g = Repeat.body f g` for any candidate `g`. -/
@[inline] abbrev Repeat.body (f : α → m (α ⊕ β)) (cont : α → m β) (a : α) : m β := do
  match ← f a with
  | .inl a' => cont a'
  | .inr a' => pure a'

/-- Step relation: `a' ≺ a` iff `f a` may return `.inl a'`. -/
def IsPlausibleStep (f : α → m (α ⊕ β)) : α → α → Prop :=
  fun a' a => MayReturnM (f a) (.inl a')

/-- The partial-def's pinning predicate. Gates on **per-point Acc** plus a structural attach:
when both hold, `v` is pinned to the value computed by `Acc.recOn` against the chosen attach.
When the gate fails, the predicate is trivially `True`. -/
private noncomputable def RepeatPred (f : α → m (α ⊕ β)) (a : α) : m β → Prop :=
  open scoped Classical in
  if h : Acc (IsPlausibleStep f) a ∧
      ∃ attach : (x : α) → m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' x},
        ∀ x, Subtype.val <$> attach x = f x then
    fun v => v = h.1.recOn (motive := fun x _ => m β) (fun _ _ ih => do
      let ⟨s, hp⟩ ← h.2.choose _
      match s, hp with
      | .inl x', hp => ih x' (hp x' rfl)
      | .inr b, _ => pure b)
  else
    fun _ => True

private instance [Nonempty β] {f : α → m (α ⊕ β)} {a : α} :
    Nonempty (Subtype (RepeatPred f a)) := by
  by_cases h : Acc (IsPlausibleStep f) a ∧
      ∃ attach : (x : α) → m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' x},
        ∀ x, Subtype.val <$> attach x = f x
  · refine ⟨⟨h.1.recOn (motive := fun x _ => m β) (fun _ _ ih => do
        let ⟨s, hp⟩ ← h.2.choose _
        match s, hp with
        | .inl x', hp => ih x' (hp x' rfl)
        | .inr b, _ => pure b), ?_⟩⟩
    simp [RepeatPred, h]
  · exact ⟨⟨pure (Classical.choice inferInstance), by simp [RepeatPred, h]⟩⟩

/-- INTERNAL. Computational core: at each `a`, returns the loop value packaged with the
new `RepeatPred` predicate. -/
@[specialize] private partial def Repeat.loop.impl [Nonempty β] [LawfulMonad m]
    (f : α → m (α ⊕ β)) (a : α) :
    Subtype (RepeatPred f a) :=
  ⟨Repeat.body f (Repeat.loop.impl f · |>.val) a, by
    simp only [RepeatPred]
    split <;> rename_i h
    · -- gate true at a; prove the body equals the Acc.recOn value over the gate's attach.
      suffices key : ∀ x (h_x : Acc (IsPlausibleStep f) x),
          Repeat.body f (Repeat.loop.impl f · |>.val) x =
          h_x.recOn (motive := fun y _ => m β) (fun y _ ih => do
            let ⟨s, hp⟩ ← h.2.choose y
            match s, hp with
            | .inl y', hp => ih y' (hp y' rfl)
            | .inr b, _ => pure b) from key a h.1
      intro x h_x
      induction h_x with
      | intro x next ih =>
        simp only [Repeat.body]
        rw [show f x = Subtype.val <$> h.2.choose x from (h.2.choose_spec x).symm, bind_map_left]
        apply bind_congr
        rintro ⟨s, hp⟩
        cases s with
        | inr b => rfl
        | inl x' =>
          show (Repeat.loop.impl f x').val = _
          have h_x' : Acc (IsPlausibleStep f) x' ∧
              ∃ attach : (y : α) → m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' y},
                ∀ y, Subtype.val <$> attach y = f y :=
            ⟨next x' (hp x' rfl), h.2⟩
          have hp_x' := (Repeat.loop.impl f x').property
          simp only [RepeatPred, dif_pos h_x'] at hp_x'
          rw [hp_x']
    · trivial⟩

/-- `Repeat.loop f a` iterates `f` at `a`. -/
@[inline] def Repeat.loop [Nonempty β] [LawfulMonad m] (f : α → m (α ⊕ β)) (a : α) : m β :=
  (Repeat.loop.impl f a).val

end Definition

section Termination

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- A user-supplied variant: for every `a`, `f a` lifts to a Subtype where yields decrease `μ`.
The lift is the constructive enriched body needed to build a global fixpoint. -/
def IsRepeatVariant {γ : Sort _} [WellFoundedRelation γ]
    (μ : α → γ) (f : α → m (α ⊕ β)) : Prop :=
  ∀ a, ∃ y : m {s : α ⊕ β // ∀ a', s = .inl a' → WellFoundedRelation.rel (μ a') (μ a)},
    Subtype.val <$> y = f a

/-- The variant implies `IsPlausibleStep` decrease, via `MayReturnM`. -/
theorem IsRepeatVariant.step {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (α ⊕ β)}
    (hvar : IsRepeatVariant μ f) {a a' : α} (h : IsPlausibleStep f a' a) :
    WellFoundedRelation.rel (μ a') (μ a) :=
  let ⟨y, hy⟩ := hvar a
  MayReturnM.imp _ h y hy a' rfl

/-- Under a variant, every `a` is accessible. -/
private theorem IsRepeatVariant.acc {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (α ⊕ β)}
    (hvar : IsRepeatVariant μ f) (a : α) : Acc (IsPlausibleStep f) a :=
  Subrelation.accessible (r := InvImage WellFoundedRelation.rel μ)
    (fun {a' b} h => hvar.step h)
    (InvImage.accessible μ (WellFoundedRelation.wf.apply (μ a)))

/-- The variant proof gives a classically-attached body via `Classical.choose`. -/
private noncomputable def attachByVariant {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (α ⊕ β)} (hvar : IsRepeatVariant μ f) (a : α) :
    m {s : α ⊕ β // ∀ a', s = .inl a' → WellFoundedRelation.rel (μ a') (μ a)} :=
  (hvar a).choose

private theorem attachByVariant_eq {γ : Sort _} [WellFoundedRelation γ]
    {μ : α → γ} {f : α → m (α ⊕ β)} (hvar : IsRepeatVariant μ f) (a : α) :
    Subtype.val <$> attachByVariant hvar a = f a :=
  (hvar a).choose_spec

end Termination

section UnfoldAtPoint

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m] {β : Type u} {f : α → m (α ⊕ β)}

/-- `MonadAttach.CanReturn` implies our `MayReturnM` (assuming `LawfulMonadAttach`). -/
theorem MayReturnM.of_canReturn {x : m α} {a : α}
    (h : MonadAttach.CanReturn x a) : MayReturnM x a := by
  intro ⟨y, hy⟩
  rw [← hy] at h
  exact LawfulMonadAttach.canReturn_map_imp h rfl

/-- Build the structural attach using `MonadAttach.attach`. -/
private noncomputable def attachFromMonadAttach (x : α) :
    m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' x} :=
  (fun ⟨s, hCR⟩ => ⟨s, fun a' heq => MayReturnM.of_canReturn (heq ▸ hCR)⟩) <$>
    MonadAttach.attach (f x)

private theorem attachFromMonadAttach_val (x : α) :
    Subtype.val <$> attachFromMonadAttach (f := f) x = f x := by
  unfold attachFromMonadAttach
  rw [← LawfulFunctor.comp_map]
  exact WeaklyLawfulMonadAttach.map_attach

/-- **Per-point unfolding.** Under `LawfulMonadAttach m` and `Acc (IsPlausibleStep f) a`,
`Repeat.loop f a` unfolds to one step. -/
theorem Repeat.loop.unfold_at [Nonempty β]
    (a : α) (h : Acc (IsPlausibleStep f) a) :
    Repeat.loop f a = Repeat.body f (Repeat.loop f) a := by
  have hGate : Acc (IsPlausibleStep f) a ∧
      ∃ attach : (x : α) → m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' x},
        ∀ x, Subtype.val <$> attach x = f x :=
    ⟨h, ⟨attachFromMonadAttach, attachFromMonadAttach_val⟩⟩
  have hp_a := (Repeat.loop.impl f a).property
  simp only [RepeatPred, dif_pos hGate] at hp_a
  show (Repeat.loop.impl f a).val = Repeat.body f (fun b => (Repeat.loop.impl f b).val) a
  rw [hp_a]
  -- Now: Acc.recOn at a using hGate.2.choose = body f (impl · |>.val) a.
  -- Same shape as the body proof's `key` — Acc-induction.
  suffices key : ∀ x (h_x : Acc (IsPlausibleStep f) x),
      Repeat.body f (Repeat.loop.impl f · |>.val) x =
      h_x.recOn (motive := fun y _ => m β) (fun y _ ih => do
        let ⟨s, hp⟩ ← hGate.2.choose y
        match s, hp with
        | .inl y', hp => ih y' (hp y' rfl)
        | .inr b, _ => pure b) from (key a hGate.1).symm
  intro x h_x
  induction h_x with
  | intro x next ih =>
    simp only [Repeat.body]
    rw [show f x = Subtype.val <$> hGate.2.choose x from (hGate.2.choose_spec x).symm, bind_map_left]
    apply bind_congr
    rintro ⟨s, hp⟩
    cases s with
    | inr b => rfl
    | inl x' =>
      show (Repeat.loop.impl f x').val = _
      have h_x' : Acc (IsPlausibleStep f) x' ∧
          ∃ attach : (y : α) → m {s : α ⊕ β // ∀ a', s = .inl a' → IsPlausibleStep f a' y},
            ∀ y, Subtype.val <$> attach y = f y :=
        ⟨next x' (hp x' rfl), hGate.2⟩
      have hp_x' := (Repeat.loop.impl f x').property
      simp only [RepeatPred, dif_pos h_x'] at hp_x'
      rw [hp_x']

end UnfoldAtPoint

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
