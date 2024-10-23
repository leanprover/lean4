/-!
# Tests of elabAsElim elaborator and the `elab_as_elim` attribute
-/

-- For debugging:
-- set_option trace.Elab.app.elab_as_elim true

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def f1 (xs : Vec α n) : Nat :=
  Vec.casesOn xs 0 fun _ _ => 1

/-! Under-applied eliminator, and expected type isn't a pi type. -/
/--
error: failed to elaborate eliminator, insufficient number of arguments, expected type:
  Nat
-/
#guard_msgs in
def f2 (xs : Vec α n) : Nat :=
  xs.casesOn 0

def f3 (x : Nat) : Nat → (Nat → Nat) → Nat :=
  x.casesOn

/-! Under-applied eliminator, expected type's binders do not unify with remaining arguments. -/
/--
error: failed to elaborate eliminator, insufficient number of arguments, expected type:
  (Nat → Nat) → Nat → Nat
-/
#guard_msgs in
def f3' (x : Nat) : (Nat → Nat) → Nat → Nat :=
  x.casesOn

def f4 (xs : List Nat) : xs ≠ [] → xs.length > 0 :=
  xs.casesOn (by intros; contradiction) (by intros; simp_arith)

def f5 (xs : List Nat) (h : xs ≠ []) : xs.length > 0 :=
  xs.casesOn (by intros; contradiction) (by intros; simp_arith) h

def f6 (x : Nat) :=
  2 * x.casesOn 0 id

example : f6 (x+1) = 2*x := rfl

/-- error: failed to elaborate eliminator, unused named arguments: [a] -/
#guard_msgs in
def f7 (xs : Vec α n) : Nat :=
  xs.casesOn (a := 10) 0

def f8 (xs : List Nat) : xs ≠ [] → xs.length > 0 :=
  @List.casesOn _ (fun xs => xs ≠ [] → xs.length > 0) xs (by dsimp; intros; contradiction) (by dsimp; intros; simp_arith)

def f5' (xs : List Nat) (h : xs ≠ []) : xs.length > 0 :=
  xs.casesOn (fun h => absurd rfl h) (fun _ _ _ => Nat.zero_lt_succ ..) h

example (h₁ : a = b) (h₂ : b = c) : a = c :=
  Eq.rec h₂ h₁.symm

@[elab_as_elim] theorem subst {p : (b : α) → a = b → Prop} (h₁ : a = b) (h₂ : p a rfl) : p b h₁ := by
  cases h₁
  assumption

example (h₁ : a = b) (h₂ : b = c) : a = c :=
  subst h₁.symm h₂

theorem not_or_not : (¬p ∨ ¬q) → ¬(p ∧ q) := λ h ⟨hp, hq⟩ =>
  h.rec (λ h1 => h1 hp) (λ h2 => h2 hq)

structure Point where
  x : Nat

theorem PointExt_lean4 (p : Point) : forall (q : Point) (h1 : Point.x p = Point.x q), p = q :=
  Point.recOn p <|
   fun z1 q => Point.recOn q $
   fun z2 (hA : Point.x (Point.mk z1) = Point.x (Point.mk z2)) => congrArg Point.mk hA

inductive pos_num : Type
  | one  : pos_num
  | bit1 : pos_num → pos_num
  | bit0 : pos_num → pos_num

inductive num : Type
  | zero  : num
  | pos   : pos_num → num

inductive znum : Type
  | zero : znum
  | pos  : pos_num → znum
  | neg  : pos_num → znum

def pos_num.pred' : pos_num → num
  | one    => .zero
  | bit0 n => num.pos (num.casesOn (pred' n) one bit1)
  | bit1 n => num.pos (bit0 n)

protected def znum.bit1 : znum → znum
  | zero    => pos .one
  | pos n => pos (pos_num.bit1 n)
  | neg n => neg (num.casesOn (pos_num.pred' n) .one pos_num.bit1)

example (h : False) : a = c :=
  h.rec

example (h : False) : a = c :=
  h.elim

noncomputable def f : Nat → Nat :=
  Nat.rec 0 (fun x _ => x)

example : ∀ x, x ≥ 0 :=
  Nat.rec (Nat.le_refl 0) (fun _ ih => Nat.le_succ_of_le ih)

/-!
Tests of `@[elab_as_elim]` when the motive is not type correct.
-/

@[elab_as_elim]
def Foo.induction {P : (α : Type) → Prop} (α : Type) : P α := sorry

/--
error: failed to elaborate eliminator, motive is not type correct:
  fun x => T = T
-/
#guard_msgs in
example {n : Type} {T : n} : T = T := Foo.induction n

/--
error: failed to elaborate eliminator, motive is not type correct:
  fun x => T✝ = T✝
-/
#guard_msgs in
example {n : Type} : {T : n} → T = T := Foo.induction n

example {n : Type} : (T : n) → T = T := Foo.induction n

-- Disable implicit lambda
example {n : Type} : {T : n} → T = T := @(Foo.induction n)

/-!
A "motive is not type correct" regression test.
The `isEmptyElim` was failing due to being under-applied and the named `(α := α)` argument
having postponed elaboration. This fix is that `α` now elaborates eagerly.
-/

class IsEmpty (α : Sort u) : Prop where
  protected false : α → False

@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim

def Set (α : Type u) := α → Prop
def Set.univ {α : Type _} : Set α := fun _ => True
instance : Membership α (Set α) := ⟨fun s x => s x⟩
def Set.pi {α : ι → Type _} (s : Set ι) (t : (i : ι) → Set (α i)) : Set ((i : ι) → α i) := fun f => ∀ i ∈ s, f i ∈ t i

example {α : Type u} [IsEmpty α] {β : α → Type v} (x : (a : α) → β a) (s : (i : α) → Set (β i)) :
    x ∈ Set.univ.pi s := isEmptyElim (α := α)

-- Simplified version:
example {α : Type _} [IsEmpty α] :
  id (α → False) := isEmptyElim (α := α)

/-!
From mathlib, regression test. Need to eagerly elaborate the `n ≤ m` argument to deduce `m`
before computing the motive.
-/

@[elab_as_elim]
def leRecOn {C : Nat → Sort _} {n : Nat} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m :=
  sorry

theorem leRecOn_self {C : Nat → Sort _} {n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x :=
  sorry

/-!
Issue https://github.com/leanprover/lean4/issues/4347

`False.rec` has `motive` as an explicit argument.
-/

example (h : False) : Nat := False.rec (fun _ => Nat) h
example (h : False) : Nat := False.rec _ h
example (h : False) : Nat := h.rec
example (h : False) : Nat := h.rec _

/-!
Check that the overapplied arguments given to the eliminator are not permuted.
In this example, `h0` and `h1` used to be reversed, leading to a kernel typechecking error.
-/
example (n : Nat) (h0 : n ≠ 0) (h1 : n ≠ 1) : n - 2 ≠ n - 1 :=
  Nat.recOn n (by simp) (by rintro (_ | _) <;> simp) h0 h1

/-!
Check that eliminators need at least one discriminant
-/

/--
error: unexpected eliminator resulting type
  p
-/
#guard_msgs in
@[elab_as_elim]
theorem mySillyEliminator {p : Prop} (h : p) : p := h
