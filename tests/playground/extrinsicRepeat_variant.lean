import Std

set_option mvcgen.warning false

/-!
# `Repeat.loop`: a classically-defined `repeat`/`while` loop combinator

`Repeat.loop f a` iterates `f : α → m (α ⊕ β)` at `a`, recursing on `.inl` and terminating on
`.inr`. The definition needs only `[Monad m] [Nonempty β]` — *no* monad laws. Termination is
*extrinsic*: `Repeat.loop.unfold_at` exposes the body only at points with
`Acc (IsPlausibleStep f) a`, where `IsPlausibleStep f a' a := MayReturnM (f a) (.inl a')`.

## Encoding

`ErasesToM y x := ∀ k, y >>= (fun a => k a.val) = x >>= k` packages bind-faithfulness as a
single quantified equation. Used in `MayReturnM` and `RepeatPred`'s gate, it side-steps any
`<$>` / `bind_pure_comp` bridging in the *core*. Lawfulness surfaces only in the bridges to
`MonadAttach` and in the spec proof.

## Sections
- **Core** (`[Bind m]` / `[Monad m]`): `ErasesToM`, `MayReturnM`, `Repeat.body`,
  `IsPlausibleStep`, `RepeatPred`, `Repeat.loop.impl`, `Repeat.loop`.
- **Lawful bridges**: `MonadAttach.attach_erases`, `MayReturnM.{of_canReturn,canReturn}`,
  `Repeat.loop.unfold_at`.
- **Spec** (`[WPMonad m ps]`): `Spec.Repeat.loop`, `Acc`-from-variant helpers.
- **`sqrt` + `possiblyDivergentLoop` examples** — end-to-end via `mvcgen`.
-/

/-- `x` "erases to" `y`: binding `x` and discarding the property is the same as binding `y`
directly. A single quantified equation packaging the bind-faithfulness we need. -/
def ErasesToM {α : Type u} {m : Type u → Type v} [Bind m] {P : α → Prop}
    (x : m {b : α // P b}) (y : m α) : Prop :=
  ∀ {β} (k : α → m β), x >>= (fun a => k a.val) = y >>= k

/-- `MayReturnM x a`: `x` cannot be lifted to `m {b // b ≠ a}` while erasing back to `x`. The
classical-image-membership analogue of `MonadAttach.CanReturn`, defined at `[Bind m]`. -/
def MayReturnM {m : Type u → Type v} [Bind m] {α : Type u} (x : m α) (a : α) : Prop :=
  ¬ ∃ y : m {b : α // b ≠ a}, ErasesToM y x

/-- Discharge a postcondition from `MayReturnM`: if `x` erases from `m {b // P b}`, then `P`
holds at every value `x` may return. (Classical, via the singleton predicate.) -/
theorem MayReturnM.imp {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u}
    {x : m α} {P : α → Prop} (a : α) (hCR : MayReturnM x a)
    (y : m {b // P b}) (hy : ErasesToM y x) : P a :=
  Classical.byContradiction fun hPa => hCR
    ⟨y >>= fun b => pure ⟨b.val, fun heq => hPa (heq ▸ b.property)⟩,
     fun k => by simp only [bind_assoc, pure_bind]; exact hy k⟩

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
  if h : Acc (IsPlausibleStep f) a ∧ ∃ attachF : (x : α) → m { s : α ⊕ β // MayReturnM (f x) s },
      ∀ x, ErasesToM (attachF x) (f x) then
    fun v => v = h.1.recOn (motive := fun _ _ => m β) (fun _ _ ih => do
      let ⟨s, hp⟩ ← h.2.choose _
      match s, hp with
      | .inl x', hp => ih x' hp
      | .inr b, _ => pure b)
  else
    fun _ => True

private instance [Nonempty β] {f : α → m (α ⊕ β)} {a : α} :
    Nonempty (Subtype (RepeatPred f a)) := by
  by_cases h : Acc (IsPlausibleStep f) a ∧
      ∃ refinedF : (x : α) → m { s : α ⊕ β // MayReturnM (f x) s },
        ∀ x, ErasesToM (refinedF x) (f x)
  · refine ⟨⟨h.1.recOn (motive := fun x _ => m β) (fun _ _ ih => do
        let ⟨s, hp⟩ ← h.2.choose _
        match s, hp with
        | .inl x', hp => ih x' hp
        | .inr b, _ => pure b), ?_⟩⟩
    simp only [RepeatPred, dif_pos h]
  · exact ⟨⟨pure (Classical.choice inferInstance), by simp only [RepeatPred, dif_neg h]⟩⟩

/-- INTERNAL. Computational core: at each `a`, returns the loop value packaged with the
`RepeatPred` predicate. The pred-proof Acc-inducts at `a`, replacing `f x` with
`h.2.choose x` via `ErasesToM`, then applies `bind_congr` and recurses through `(impl f x').property`. -/
@[specialize] private partial def Repeat.loop.impl [Nonempty β]
    (f : α → m (α ⊕ β)) (a : α) :
    Subtype (RepeatPred f a) :=
  ⟨Repeat.body f (Repeat.loop.impl f · |>.val) a, by
    simp only [RepeatPred]
    split <;> rename_i h
    · suffices key : ∀ x (h_x : Acc (IsPlausibleStep f) x),
          Repeat.body f (Repeat.loop.impl f · |>.val) x =
          h_x.recOn (motive := fun _ _ => m β) (fun _ _ ih => do
            let ⟨s, hp⟩ ← h.2.choose _
            match s, hp with
            | .inl x', hp => ih x' hp
            | .inr b, _ => pure b) from key a h.1
      intro x h_x
      induction h_x with
      | intro x next ih =>
        simp only [Repeat.body]
        rw [← (h.2.choose_spec x)]
        apply bind_congr
        rintro ⟨s, hp⟩
        cases s with
        | inr b => rfl
        | inl x' =>
          show (Repeat.loop.impl f x').val = _
          have h_x' : Acc (IsPlausibleStep f) x' ∧ _ := ⟨next x' hp, h.2⟩
          have hp_x' := (Repeat.loop.impl f x').property
          simp only [RepeatPred, dif_pos h_x'] at hp_x'
          rw [hp_x']
    · trivial⟩

/-- `Repeat.loop f a` iterates `f` at `a`. -/
@[inline] def Repeat.loop [Nonempty β] (f : α → m (α ⊕ β)) (a : α) : m β :=
  (Repeat.loop.impl f a).val

end Definition

section LawfulBridges

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [WeaklyLawfulMonadAttach m]

/-- `MonadAttach.attach` erases to its argument: the canonical `ErasesToM` witness. -/
theorem MonadAttach.attach_erases {x : m α} : ErasesToM (MonadAttach.attach x) x := by
  intro β k; rw [← bind_map_left, WeaklyLawfulMonadAttach.map_attach]

/-- Bridge from `MayReturnM` back to `MonadAttach.CanReturn`. -/
theorem MayReturnM.canReturn {x : m α} {a : α} (h : MayReturnM x a) :
    MonadAttach.CanReturn x a :=
  MayReturnM.imp a h (MonadAttach.attach x) MonadAttach.attach_erases

end LawfulBridges

section UnfoldAtPoint

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m] {β : Type u} {f : α → m (α ⊕ β)}

/-- `MonadAttach.CanReturn` implies our `MayReturnM` (under `LawfulMonadAttach`). -/
theorem MayReturnM.of_canReturn {x : m α} {a : α}
    (h : MonadAttach.CanReturn x a) : MayReturnM x a := by
  intro ⟨y, hy⟩
  have hy_map : Subtype.val <$> y = x := by simpa [← bind_pure_comp] using hy pure
  rw [← hy_map] at h
  exact LawfulMonadAttach.canReturn_map_imp h rfl

/-- **Per-point unfolding.** Under `Acc (IsPlausibleStep f) a`, `Repeat.loop f a` unfolds to
one step. Gate is `MonadAttach.attach` refined with `MayReturnM` witnesses; Acc-induction
mirrors `impl`'s pred-proof. -/
theorem Repeat.loop.unfold_at [Nonempty β]
    (a : α) (h : Acc (IsPlausibleStep f) a) :
    Repeat.loop f a = Repeat.body f (Repeat.loop f) a := by
  have hGate : Acc (IsPlausibleStep f) a ∧
      ∃ attachF : (x : α) → m { s : α ⊕ β // MayReturnM (f x) s },
        ∀ x, ErasesToM (attachF x) (f x) :=
    ⟨h, fun x => (fun ⟨s, hCR⟩ => ⟨s, MayReturnM.of_canReturn hCR⟩) <$> MonadAttach.attach (f x),
        fun x β k => by rw [bind_map_left]; exact MonadAttach.attach_erases k⟩
  have hp_a := (Repeat.loop.impl f a).property
  simp only [RepeatPred, dif_pos hGate] at hp_a
  show (Repeat.loop.impl f a).val = _
  rw [hp_a]
  suffices key : ∀ x (h_x : Acc (IsPlausibleStep f) x),
      Repeat.body f (Repeat.loop.impl f · |>.val) x =
      h_x.recOn (motive := fun _ _ => m β) (fun _ _ ih => do
        let ⟨s, hp⟩ ← hGate.2.choose _
        match s, hp with
        | .inl x', hp => ih x' hp
        | .inr b, _ => pure b) from (key a hGate.1).symm
  intro x h_x
  induction h_x with
  | intro x next ih =>
    simp only [Repeat.body]
    rw [← (hGate.2.choose_spec x)]
    apply bind_congr
    rintro ⟨s, hp⟩
    cases s with
    | inr b => rfl
    | inl x' =>
      show (Repeat.loop.impl f x').val = _
      have h_x' : Acc (IsPlausibleStep f) x' ∧ _ := ⟨next x' hp, hGate.2⟩
      have hp_x' := (Repeat.loop.impl f x').property
      simp only [RepeatPred, dif_pos h_x'] at hp_x'
      rw [hp_x']

end UnfoldAtPoint

section Spec

open Std.Do

/-- An invariant for a `Repeat.loop`. -/
@[spec_invariant_type]
abbrev RepeatSumInvariant (α β : Type u) (ps : PostShape.{u}) := PostCond (α ⊕ β) ps

variable {α β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] [WPMonad m ps]

/-- Per-point unfolding factored through `MonadAttach.attach`. After the rewrite, the body
exposes a `MonadAttach.CanReturn (f a) s` witness that bridges to `IsPlausibleStep f a' a`
for the `.inl a'` branch — what the spec needs to recurse on the `Acc` IH. -/
private theorem Repeat.loop.unfold_at_attach
    {f : α → m (α ⊕ β)} [Nonempty β]
    (a : α) (h : Acc (IsPlausibleStep f) a) :
    Repeat.loop f a = (MonadAttach.attach (f a) >>= fun x =>
      match x.val with
      | .inl a' => Repeat.loop f a'
      | .inr b => pure b) := by
  rw [Repeat.loop.unfold_at a h]
  show (f a >>= fun s => match s with
      | .inl a' => Repeat.loop f a'
      | .inr a' => pure a') = _
  exact (MonadAttach.attach_erases _).symm

/-- `@[spec]` theorem for `Repeat.loop`. Takes `hAcc : Acc (IsPlausibleStep f) init` directly,
so the user controls termination at the call site (per-point Acc, not global wf). The two
`acc_of_*` helpers below produce `Acc` from a measure. -/
@[spec]
theorem Spec.Repeat.loop
    {init : α} {f : α → m (α ⊕ β)} [Nonempty β]
    (hAcc : Acc (IsPlausibleStep f) init)
    (inv : RepeatSumInvariant α β ps)
    (step : ∀ a,
      Triple (f a) (inv.1 (.inl a))
        (fun r => match r with
          | .inl a' => inv.1 (.inl a')
          | .inr b => inv.1 (.inr b), inv.2)) :
    Triple (Repeat.loop f init) (inv.1 (.inl init))
        (fun b => inv.1 (.inr b), inv.2) := by
  induction hAcc with
  | intro a next ih =>
  rw [Repeat.loop.unfold_at_attach a (Acc.intro a next)]
  mvcgen [step]
  rename_i stp
  apply SPred.forall_intro
  intro hCR
  cases stp with
  | inl a' => exact Triple.iff.mp (ih a' (MayReturnM.of_canReturn hCR))
  | inr b => mvcgen

end Spec

section AccHelpers

open Std.Do

variable {α β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] [WPAdequacy m ps]

/-- Bridge: from `MayReturnM x a` and a Triple proving a `Prop` post `P`, conclude `P a`. -/
theorem MayReturnM.adequate {x : m α} {P : α → Prop} {a : α}
    (hMR : MayReturnM x a) (h_triple : ⦃⌜True⌝⦄ x ⦃⇓ r => ⌜P r⌝⦄) : P a := by
  have h' : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝) := by
    apply SPred.entails.trans (Triple.iff.mp h_triple)
    apply (wp x).mono; simp [PostCond.entails]
  exact WPAdequacy.adequate h' a hMR.canReturn

/-- Build `Acc (IsPlausibleStep f) init` from an *unconditional* measure-decrease WP fact.
Use this when the loop body's structure (e.g. `if guard then yield else done`) makes the
variant decrease unconditionally. -/
theorem Repeat.IsPlausibleStep.acc_of_wp_measure
    {f : α → m (α ⊕ β)} (measure : α → Nat) (init : α)
    (h : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r => ⌜∀ a', r = .inl a' → measure a' < measure a⌝⦄) :
    Acc (IsPlausibleStep f) init := by
  apply Subrelation.accessible (r := InvImage Nat.lt measure) ?_
    (InvImage.accessible measure (Nat.lt_wfRel.wf.apply (measure init)))
  intro a' a hStep
  exact hStep.adequate (h a) a' rfl

/-- Build `Acc (IsPlausibleStep f) init` from a Prop predicate `P` preserved along yields and a
measure that decreases at `P`-satisfying points. Use this for loops that only terminate under a
precondition (e.g. `possiblyDivergentLoop`). -/
theorem Repeat.IsPlausibleStep.acc_of_wp_measure_under
    {f : α → m (α ⊕ β)} (P : α → Prop) (measure : α → Nat) (init : α) (hP : P init)
    (h : ∀ a, P a → ⦃⌜True⌝⦄ f a ⦃⇓ r =>
      ⌜∀ a', r = .inl a' → measure a' < measure a ∧ P a'⌝⦄) :
    Acc (IsPlausibleStep f) init := by
  suffices h_helper : ∀ n init, P init → measure init = n → Acc (IsPlausibleStep f) init from
    h_helper _ _ hP rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro init hP hmeas
    refine Acc.intro _ fun a' hStep => ?_
    have hpost := hStep.adequate (h init hP) a' rfl
    exact ih (measure a') (hmeas ▸ hpost.1) a' hpost.2 rfl

end AccHelpers

section SqrtExample

open Std.Do

/-- `MayReturnM` for `Id` reduces to equality. -/
@[simp] theorem MayReturnM_id {α : Type u} {x : Id α} {a : α} :
    MayReturnM x a ↔ x = a := by
  constructor
  · intro h
    refine Classical.byContradiction fun hne => h ⟨⟨x, hne⟩, fun _ => rfl⟩
  · intro hxa h
    obtain ⟨y, hy⟩ := h
    have := hy pure
    simp at this
    exact y.property (hxa ▸ this)

/-- `sqrt n` computes the integer square root of `n` using `Repeat.loop`. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let res ← Repeat.loop
    (fun i => pure (if i * i ≤ n then .inl (i + 1) else .inr i))
    0
  return res - 1

/-- The `sqrt` function returns the correct integer square root. -/
theorem sqrt_correct :
    ⦃⌜True⌝⦄ sqrt n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res + 1)⌝⦄ := by
  have hAcc : Acc (IsPlausibleStep (m := Id)
      (fun i => pure (if i * i ≤ n then .inl (i + 1) else .inr i))) 0 := by
    apply Repeat.IsPlausibleStep.acc_of_wp_measure (measure := fun i => (n + 2) - i)
    intro a
    mvcgen
    intro a' h
    split at h
    · injection h with heq; subst heq
      have : a ≤ a * a := Nat.le_mul_self a
      omega
    · cases h
  mvcgen [sqrt, hAcc]
  invariants
  | inv1 => ⇓ cursor => match cursor with
    | .inl i => ⌜∀ j, j < i → j * j ≤ n⌝
    | .inr i => ⌜(∀ j, j < i → j * j ≤ n) ∧ n < i * i⌝
  with (try grind)
  | vc5.isFalse.post.success res h =>
    have : res - 1 < res := by grind
    grind

#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 100) == 10

/-- A loop that does not terminate for all inputs — only for `x ≤ 20`. -/
def possiblyDivergentLoop (x : Nat) : Id Nat :=
  Repeat.loop (fun i => pure (if i ≠ 20 then .inl (i + 1) else .inr i)) x

example (hx : x ≤ 20) : ⦃⌜True⌝⦄ possiblyDivergentLoop x ⦃⇓ r => ⌜r = 20⌝⦄ := by
  have hAcc : Acc (IsPlausibleStep (m := Id)
      (fun i => pure (if i ≠ 20 then .inl (i + 1) else .inr i))) x := by
    apply Repeat.IsPlausibleStep.acc_of_wp_measure_under
      (P := fun i => i ≤ 20) (measure := fun i => 20 - i) (init := x) hx
    intro a hP
    mvcgen
    intro a' h
    split at h <;> grind
  mvcgen [possiblyDivergentLoop, hAcc]
  invariants
  | inv1 => ⇓ cursor => match cursor with
    | .inl i => ⌜i ≤ 20⌝
    | .inr i => ⌜i = 20⌝
  with grind

end SqrtExample
