inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def f1 (xs : Vec α n) : Nat :=
  Vec.casesOn xs 0 fun _ _ => 1

def f2 (xs : Vec α n) : Nat :=
  xs.casesOn 0 -- Error insufficient number of arguments

def f3 (x : Nat) : Nat → (Nat → Nat) → Nat :=
  x.casesOn

def f4 (xs : List Nat) : xs ≠ [] → xs.length > 0 :=
  xs.casesOn (by intros; contradiction) (by intros; simp_arith)

def f5 (xs : List Nat) (h : xs ≠ []) : xs.length > 0 :=
  xs.casesOn (by intros; contradiction) (by intros; simp_arith) h

def f6 (x : Nat) :=
  2 * x.casesOn 0 id

example : f6 (x+1) = 2*x := rfl

def f7 (xs : Vec α n) : Nat :=
  xs.casesOn (a := 10) 0 -- Error unused named args

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
