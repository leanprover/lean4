-- Since we do not have ENNReal in core, we just axiomatize it all for this test

opaque ENNReal : Type

axiom ENNReal.sup : ∀ {α}, (α → ENNReal) → ENNReal
axiom ENNReal.sum : ∀ {α}, (α → ENNReal) → ENNReal
axiom ENNReal.add : ENNReal → ENNReal → ENNReal
axiom ENNReal.mul : ENNReal → ENNReal → ENNReal

noncomputable instance : Add ENNReal where add := .add
noncomputable instance : Mul ENNReal where mul := .mul
@[instance] axiom ENNReal.zero : Zero ENNReal
axiom ENNReal.one : ENNReal
axiom ENNReal.one_half : ENNReal

@[simp] axiom ENNReal.mul_one : ∀ x, x * ENNReal.one = x
@[simp] axiom ENNReal.mul_zero : ∀ (x : ENNReal), x * 0 = 0
@[simp] axiom ENNReal.add_zero : ∀ (x : ENNReal), x + 0 = x
@[simp] axiom ENNReal.zero_add : ∀ (x : ENNReal), 0 + x = x
@[simp] axiom ENNReal.sum_bool : ∀ f, sum f = f true + f false
@[simp] axiom ENNReal.sum_const_zero : ∀ α, ENNReal.sum (fun (_ : α) => 0) = 0
@[simp] axiom ENNReal.sum_dirac : ∀ α [DecidableEq α] (f : α → ENNReal) y,
  ENNReal.sum (fun x => if x = y then f x else 0) = f y

@[instance] axiom ENNReal.le : LE ENNReal
axiom ENNReal.le_refl : ∀ (x : ENNReal), x ≤ x
axiom ENNReal.le_trans : ∀ {x y z: ENNReal}, x ≤ y → y ≤ z → x ≤ z
axiom ENNReal.le_antisymm : ∀ {x y : ENNReal}, x ≤ y → y ≤ x → x = y

section
set_option linter.unusedVariables false
axiom ENNReal.sum_mono : ∀ {α} (s₁ s₂ : α → ENNReal) (h : ∀ x, s₁ x ≤ s₂ x),
  ENNReal.sum s₁ ≤ ENNReal.sum s₂
axiom ENNReal.sup_mono : ∀ {α} (s₁ s₂ : α → ENNReal) (h : ∀ x, s₁ x ≤ s₂ x),
  ENNReal.sup s₁ ≤ ENNReal.sup s₂
axiom ENNReal.mul_mono : ∀ (a b c Distr : ENNReal) (h₁ : a ≤ c) (h₂ : b ≤ Distr),
  a * b ≤ c * Distr

axiom ENNReal.le_sup : ∀ {α} (a : ENNReal) (s : α → ENNReal) (i : α) (h : a ≤ s i),
  a ≤ ENNReal.sup s
axiom ENNReal.sup_le : ∀ {α} (a : ENNReal) (s : α → ENNReal) (h : ∀ (i : α), s i ≤ a),
  ENNReal.sup s ≤ a
end


/-- Distributions (not normalized, which is curcial, else we don't have ⊥.) -/
def Distr (α : Type) : Type := α → ENNReal

noncomputable def Distr.join : Distr (Distr α) → Distr α := fun dd x =>
  ENNReal.sum (fun Distr => Distr x * dd Distr )

noncomputable instance : Functor Distr where
  map f Distr := fun x => ENNReal.sum (fun y => open Classical in if f y = x then Distr y else 0)

noncomputable instance : Pure Distr where
  pure x := fun y => open Classical in if x = y then .one else 0

noncomputable instance : Bind Distr where
  bind Distr f := fun x => ENNReal.sum (fun y => Distr y * f y x)

open Lean.Order

noncomputable instance : PartialOrder (Distr α) where
  rel d1 d2 := ∀ x, d1 x ≤ d2 x
  rel_refl _ := ENNReal.le_refl _
  rel_trans h1 h2 _ := ENNReal.le_trans (h1 _) (h2 _)
  rel_antisymm h1 h2 := funext (fun _ => ENNReal.le_antisymm (h1 _) (h2 _))

noncomputable instance : CCPO (Distr α) where
  csup c x := ENNReal.sup fun (Distr : Subtype c) => Distr.val x
  csup_spec := by
    intros d₁ c hchain
    constructor
    next =>
      intro h d₂ hd₂ x
      apply ENNReal.le_trans ?_ (h x)
      apply ENNReal.le_sup (i := ⟨d₂, hd₂⟩)
      apply ENNReal.le_refl
    next =>
      intro h x
      apply ENNReal.sup_le
      intros Distr
      apply h Distr.1 Distr.2 x

noncomputable instance : MonoBind Distr where
  bind_mono_left := by
    intro α β d₁ d₂ f h₁₂ y
    unfold bind instBindDistr
    dsimp
    apply ENNReal.sum_mono
    intro x
    apply ENNReal.mul_mono
    · apply h₁₂
    · apply ENNReal.le_refl

  bind_mono_right := by
    intro α β Distr f₁ f₂ h₁₂ y
    apply ENNReal.sum_mono
    intro x
    apply ENNReal.mul_mono
    · apply ENNReal.le_refl
    · apply h₁₂


noncomputable def coin : Distr Bool := fun _ => .one_half

noncomputable def geom : Distr Nat := do
  let head ← coin
  if head then
    return 0
  else
    let n ← geom
    return (n + 1)
partial_fixpoint

/--
info: geom.eq_1 :
  geom = do
    let head ← coin
    if head = true then pure 0
      else do
        let n ← geom
        pure (n + 1)
-/
#guard_msgs in
#check geom.eq_1

-- And we can can do proofs about this

theorem geom_0 : geom 0 = .one_half := by
  rw [geom]; simp [bind, coin, pure]

theorem geom_succ : geom (n+1) = .one_half * geom n := by
  conv => lhs; rw [geom]
  simp [bind, coin, pure, apply_ite]
