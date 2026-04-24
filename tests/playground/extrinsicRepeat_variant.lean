import Std

/-!
# `extrinsicRepeat` with totality-gated pointwise fixpoint

`extrinsicRepeat` is gated on `HasTotalFixpoint f`, a classical witness that some `g : α → m α`
is a fixpoint of `repeatF f` *at every total point*. The condition doesn't depend on the input
`a`, so `extrinsicRepeat f = h.choose` as a function, and unfolding at a total `a` reduces
immediately to the pointwise fixpoint equation from `h.choose_spec a ha`.

`MonadAttach` + lawfulness appear only in the theorems that discharge `HasTotalFixpoint` under
a user-supplied variant.
-/

section Definition

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- One-step unfolding of the repeat loop. -/
@[inline] def repeatF (f : α → m (ForInStep α)) (cont : α → m α) (a : α) : m α := do
  match ← f a with
  | .done a' => pure a'
  | .yield a' => cont a'

partial def opaqueRepeat (f : α → m (ForInStep α)) (a : α) : m α :=
  repeatF f (opaqueRepeat f) a

def IsFix (f : α → m (ForInStep α)) (g : α → m α) : Prop :=
  g = repeatF f g

/--
`a` is *total* for `f` if every pair of fixpoints of `repeatF f` agrees at `a`.
-/
def Total (f : α → m (ForInStep α)) (a : α) : Prop :=
  ∀ g₁ g₂ : α → m α, IsFix f g₁ → IsFix f g₂ → g₁ a = g₂ a

open Classical in
/--
`extrinsicRepeat f a` iterates `f` at `a`. Same obligations as `Loop.forIn`.
-/
@[cbv_opaque, implemented_by opaqueRepeat]
def extrinsicRepeat (f : α → m (ForInStep α)) (a : α) : m α :=
  if h : ∃ g, IsFix f g ∧ Total f a then
    h.choose a
  else
    opaqueRepeat f a

/--
At a total point, `extrinsicRepeat f a` equals `g a` for any fixpoint `g`: `Total` forces all
fixpoints to agree at `a`, so the classical choice is pinned.
-/
theorem extrinsicRepeat_eq_fix {f : α → m (ForInStep α)}
    (g : α → m α) (hfix : IsFix f g) {a : α} (ha : Total f a) :
    extrinsicRepeat f a = g a := by
  have h : ∃ g, IsFix f g ∧ Total f a := ⟨g, hfix, ha⟩
  have heq : extrinsicRepeat f a = h.choose a := by simp only [extrinsicRepeat, dif_pos h]
  rw [heq]
  exact ha _ _ h.choose_spec.1 hfix

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

/-- Bind congruence using `MonadAttach.CanReturn` to supply the pointwise hypothesis. -/
theorem bind_congr_canReturn {x : m α} {k1 k2 : α → m β}
    (h : ∀ a, MonadAttach.CanReturn x a → k1 a = k2 a) : x >>= k1 = x >>= k2 := by
  rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := x) (f := k1),
      ← WeaklyLawfulMonadAttach.attach_bind_val (x := x) (f := k2)]
  exact bind_congr fun ⟨a, ha⟩ => h a ha

/--
Under a variant, widening the iteration count past `μ a + 1` doesn't change the value:
for all `N ≥ μ a + 1`, `Nat.repeat N pure a = Nat.repeat (μ a + 1) pure a`.
-/
theorem IsLoopVariant.bound_widen {μ : α → Nat} {f : α → m (ForInStep α)}
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
      · -- μ a + 1 < N + 1, so μ a + 1 ≤ N
        have hmuN : μ a + 1 ≤ N := Nat.lt_succ_iff.mp hlt
        have hmaN : μ a ≤ N := Nat.le_of_succ_le hmuN
        -- Nat.repeat (N+1) pure a = repeatF f (Nat.repeat N pure) a
        -- Nat.repeat (μ a + 1) pure a = repeatF f (Nat.repeat (μ a) pure) a
        show repeatF f (Nat.repeat (repeatF f) N pure) a =
             repeatF f (Nat.repeat (repeatF f) (μ a) pure) a
        simp only [repeatF]
        apply bind_congr_canReturn
        intro r hr
        cases r with
        | done b => rfl
        | yield a' =>
          -- μ a' < μ a, so μ a' + 1 ≤ μ a ≤ N
          have hlta : μ a' < μ a := hvar a a' hr
          have hmuaN : μ a' + 1 ≤ N := Nat.le_trans hlta hmaN
          have hmuaμa : μ a' + 1 ≤ μ a := hlta
          show Nat.repeat (repeatF f) N pure a' = Nat.repeat (repeatF f) (μ a) pure a'
          -- Use IH twice: at N and at μ a, both reach Nat.repeat (μ a' + 1) pure a'
          have h1 : Nat.repeat (repeatF f) N pure a' =
                    Nat.repeat (repeatF f) (μ a' + 1) pure a' :=
            ih N (Nat.lt_succ_self _) a' hmuaN
          have h2 : Nat.repeat (repeatF f) (μ a) pure a' =
                    Nat.repeat (repeatF f) (μ a' + 1) pure a' := by
            rcases Nat.lt_or_eq_of_le hmuaμa with hgt | heq
            · exact ih (μ a) (Nat.lt_succ_of_le hmaN) a' hmuaμa
            · rw [heq]
          rw [h1, ← h2]
      · -- μ a + 1 = N + 1
        rw [← heq]

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
Under a variant, the iterate function `g a := Nat.repeat (μ a + 1) pure a` is a global
fixpoint of `repeatF f`.
-/
theorem IsLoopVariant.hasFix {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) : ∃ g, IsFix f g := by
  refine ⟨fun a => Nat.repeat (repeatF f) (μ a + 1) pure a, ?_⟩
  show (fun a => Nat.repeat (repeatF f) (μ a + 1) pure a) =
       repeatF f (fun a => Nat.repeat (repeatF f) (μ a + 1) pure a)
  funext b
  show Nat.repeat (repeatF f) (μ b + 1) pure b =
       repeatF f (fun a => Nat.repeat (repeatF f) (μ a + 1) pure a) b
  show repeatF f (Nat.repeat (repeatF f) (μ b) pure) b =
       repeatF f (fun a => Nat.repeat (repeatF f) (μ a + 1) pure a) b
  simp only [repeatF]
  apply bind_congr_canReturn
  intro r hr
  cases r with
  | done c => rfl
  | yield b' =>
    show Nat.repeat (repeatF f) (μ b) pure b' =
         Nat.repeat (repeatF f) (μ b' + 1) pure b'
    exact hvar.bound_widen (μ b) b' (hvar b b' hr)

/--
Safe unfolding of `extrinsicRepeat f` under a variant: at every point, `extrinsicRepeat`
unfolds one step of the loop body.
-/
theorem IsLoopVariant.extrinsicRepeat_unfold {μ : α → Nat} {f : α → m (ForInStep α)}
    (hvar : IsLoopVariant μ f) (a : α) :
    extrinsicRepeat f a = repeatF f (extrinsicRepeat f) a := by
  obtain ⟨g, hfix⟩ := hvar.hasFix
  rw [extrinsicRepeat_eq_fix g hfix (hvar.total a)]
  rw [congrFun hfix a]
  simp only [repeatF]
  apply bind_congr_canReturn
  intro r hr
  cases r with
  | done b => rfl
  | yield a' =>
    exact (extrinsicRepeat_eq_fix g hfix (hvar.total a')).symm

end Termination
