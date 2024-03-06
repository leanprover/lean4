-- This is a preliminary list of aspirational goals for the new `auto` tactic.
-- I'm still trying to get a sense of the planned scope;
-- some of these may be quickly ruled out of scope!

macro "auto" : tactic => `(tactic| sorry)

namespace Nat

-- Nat.lt_asymm
example {a b : Nat} (h : a < b) : ¬ b < a :=
  Nat.not_lt.2 (Nat.le_of_lt h)
  -- If `Nat.not_lt : ¬a < b ↔ b ≤ a` is a `simp` rule,
  -- and `Nat.le_of_lt : a < b → a ≤ b` is a `have` rule:
  -- by auto

-- Nat.lt_iff_le_not_le
example {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun ⟨_, h⟩ => Nat.lt_of_not_ge h⟩
  -- Is proving `↔` via the constructor in scope? I presume so?
  -- If `Nat.not_le_of_gt : a < b → ¬b ≤ a` is an `apply` rule,
  -- and `Nat.not_le` is a `simp` rule:
  -- by auto

-- Nat.ne_iff_lt_or_gt
example {a b : Nat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨Nat.lt_or_gt_of_ne, fun | .inl h => Nat.ne_of_lt h | .inr h => Nat.ne_of_gt h⟩
  -- `Nat.lt_or_gt_of_ne : a ≠ b → a < b ∨ b < a` would be a `have` rule?
  -- We'll do cases on `Or`
  -- `Nat.ne_of_lt` and `Nat.ne_of_gt` would be `have` rules?

-- A simple logic puzzle: extract a witness from `h₂`, specialize `h₁` at it.
example (b : List α) (p : α → Prop) (h₁ : ∀ a ∈ b, p a) (h₂ : ∃ a ∈ b, ¬p a) : False :=
  by auto

-- From `Nat.testBit_two_pow_sub_succ`
example (h : x < 2 ^ (n + 1)) :
    decide ((2 ^ (n + 1) - (x + 1)) % 2 = 1) =
      (decide (0 < n + 1) && !decide (x % 2 = 1)) := by
  -- "just logic and omega":
  simp only [zero_lt_succ, decide_True, Bool.true_and]
  rw [← decide_not, decide_eq_decide]
  omega

-- From `Nat.ne_zero_implies_bit_true`
example {x : Nat}
    {hyp : x > 0 → x / 2 ≠ 0 → ∃ i, testBit (x / 2) i = true}
    {xnz : 2 * (x / 2) ≠ 0}
    {x_pos : x > 0} : ∃ i, testBit x i = true := by
  -- Is this in scope? Much harder. One has to:
  -- * Realise that in `hyp` we could replace `testBit (x / 2) i` with `testBit x (i + 1)`.
  --   (this is the simp lemma `testBit_succ` in the opposite direction)
  -- * Now see that `hyp` could be used to instantiate the existential with `i + 1`.
  -- * After that, deduce `x / 2 ≠ 0` from `xnz`.
  simp only [ne_eq, Nat.mul_eq_zero, Nat.add_zero, false_or] at xnz
  have ⟨d, dif⟩ := hyp x_pos xnz
  apply Exists.intro (d+1)
  simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, forall_const, testBit_succ]

end Nat

namespace List

-- From `List.mem_filter`
example : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  -- Is it even in scope to try induction?
  induction as with
  | nil => simp
  | cons a as ih =>
    /-
    The original proof proceeds here as:
    ```
    by_cases h : p a <;> simp [*, or_and_right]
    · exact or_congr_left (and_iff_left_of_imp fun | rfl => h).symm
    · exact (or_iff_right fun ⟨rfl, h'⟩ => h h').symm
    ```
    However it is not reasonable to get that one should use `by_cases p a` yet.
    -/
    -- It might be reasonable for `auto` to be aware of `filter_cons`,
    -- even though it is not a simp lemma.
    simp [filter_cons]
    -- Now it is reasonable to split:
    split
    · simp [*]
      sorry -- just logic from here
    · simp [*]
      sorry -- just slightly trickier logic from here


-- Recall:
-- theorem append_inj :
--     ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂

-- From `List.append_inj'`
example (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  -- It seems unreasonable for `append_inj` to be a global `apply` rule,
  -- but it could be added local, or might be reasonable as a `have` rule.
  -- In either case, after using it,
  -- `auto` would need to deduce `s₁.length = s₂.length` from `hl`.
  -- If `auto` can apply `List.length` to `h`, then after simplifying this is just arithmetic.
  auto
  -- Original proof:
  -- append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  -- let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap

end List

namespace CategoryTheory

universe v u

macro "cat_tac" : tactic => `(tactic| (intros; (try ext); simp))

class Category (obj : Type u) : Type max u (v + 1) where
  Hom : obj → obj → Type v
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : Hom X Y), comp (id X) f = f := by cat_tac
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : Hom X Y), comp f (id Y) = f := by cat_tac
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h) := by cat_tac

attribute [simp] Category.id_comp Category.comp_id Category.assoc

infixr:10 " ⟶ " => Category.Hom
scoped notation "𝟙" => Category.id  -- type as \b1
scoped infixr:80 " ≫ " => Category.comp

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂ where
  /-- The action of a functor on objects. -/
  obj : C → D
  /-- The action of a functor on morphisms. -/
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by cat_tac
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) := by cat_tac

attribute [simp] Functor.map_id Functor.map_comp

@[ext]
structure NatTrans [Category.{v₁, u₁} C] [Category.{v₂, u₂} D] (F G : Functor C D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by cat_tac

attribute [simp] NatTrans.naturality

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable {F G : Functor C D}

namespace NatTrans

protected def id (F : Functor C D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp] theorem id_app : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

protected def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := by
    intros X Y f
    dsimp
    -- This is the first place where `cat_tac` lets us down, and ematching should save us.
    -- We can't rewrite by `α.naturality f` immediately, because the composition is associated incorrectly.
    rw [← Category.assoc]
    rw [α.naturality f]
    rw [Category.assoc]
    rw [β.naturality f]
    rw [← Category.assoc]
    -- (Mathlib gets around this with a `@[reassoc]` attribute,
    -- that automatically generates copies of lemmas that fold in associativity.
    -- It can only ever get you "one step", however.)
    -- (Note that the ematching in Lean 3 couldn't quite do this one:
    -- just because there was a bug when we have two typeclass instances with different parameters,
    -- e.g. the two category instances here.)

@[simp] theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (α.vcomp β).app X = α.app X ≫ β.app X := rfl

end NatTrans

instance Functor.category : Category.{max u₁ v₂} (Functor C D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := NatTrans.vcomp α β
  -- Here we're okay: all the proofs are handled by `cat_tac`.

@[simp]
theorem id_app (F : Functor C D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp]
theorem comp_app {F G H : Functor C D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem app_naturality {F G : Functor C (Functor D E)} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f := by
  cat_tac

theorem naturality_app {F G : Functor C (Functor D E)} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z := by
  -- `simp` can't get us there, as one has to go uphill first.
  rw [← comp_app]
  rw [T.naturality f]
  rw [comp_app]


end CategoryTheory
