
set_option linter.missingDocs false
axiom mySorry {α : Sort _} : α

structure A (n : Nat) where
  a : Nat

example (a b : A n) : a = b ∨ True := by
  fail_if_success
    apply Or.inl; ext
  exact Or.inr trivial

structure B (n) extends A n where
  b : Nat
  h : b > 0
  i : Fin b

@[ext] structure C (n) extends B n where
  c : Nat

example (a b : C n) : a = b := by
  ext
  guard_target = a.a = b.a; exact mySorry
  guard_target = a.b = b.b; exact mySorry
  guard_target = HEq a.i b.i; exact mySorry
  guard_target = a.c = b.c; exact mySorry

@[ext (flat := false)] structure C' (n) extends B n where
  c : Nat

example (a b : C' n) : a = b := by
  ext
  guard_target = a.toB = b.toB; exact mySorry
  guard_target = a.c = b.c; exact mySorry

example (f g : Nat × Nat → Nat) : f = g := by
  ext ⟨x, y⟩
  guard_target = f (x, y) = g (x, y); exact mySorry

-- Check that we generate a warning if there are too many patterns.
/--
warning: `ext` did not consume the patterns: [j]
note: this linter can be disabled with `set_option linter.unusedRCasesPattern false`
-/
#guard_msgs in
example (f g : Nat → Nat) (h : f = g) : f = g := by
  ext i j
  exact h ▸ rfl

-- allow more specific ext theorems
@[ext high] theorem Fin.zero_ext (a b : Fin 0) : True → a = b := by cases a.isLt
example (a b : Fin 0) : a = b := by ext; exact True.intro

/-- info: Fin.zero_ext_iff {a b : Fin 0} : a = b ↔ True -/
#guard_msgs in #check Fin.zero_ext_iff

def Set (α : Type u) := α → Prop
@[ext] structure LocalEquiv (α : Type u) (β : Type v) where
  source : Set α
@[ext] structure Pretrivialization {F : Type u} (proj : Z → β) extends LocalEquiv Z (β × F) where
  baseSet : Set β
  source_eq : source = baseSet ∘ proj

structure MyUnit

@[ext (iff := false) high] theorem MyUnit.ext1 (x y : MyUnit) (_h : 0 = 1) : x = y := rfl
@[ext high] theorem MyUnit.ext2 (x y : MyUnit) (_h : 1 = 1) : x = y := rfl
@[ext (iff := false)] theorem MyUnit.ext3 (x y : MyUnit) (_h : 2 = 1) : x = y := rfl

/-- info: MyUnit.ext2_iff {x y : MyUnit} : x = y ↔ 1 = 1 -/
#guard_msgs in #check MyUnit.ext2_iff

example (x y : MyUnit) : x = y := by ext; rfl

-- Check that we don't generate a warning when `x` only uses a pattern in one branch:
example (f : ℕ × (ℕ → ℕ)) : f = f := by
  ext x
  · rfl
  · guard_target = (f.2) x = (f.2) x
    rfl

example (f : Empty → Empty) : f = f := by
  ext ⟨⟩

example (xs : Array α) : xs.map id = xs := by
  ext
  . simp
  . simp

@[ext (iff := false)] theorem ext_intros {n m : Nat} (w : ∀ n m : Nat, n = m) : n = m := by apply w

#guard_msgs (drop warning) in
example : 3 = 7 := by
  ext : 1
  rename_i n m
  guard_target = n = m
  admit

#guard_msgs (drop warning) in
example : 3 = 7 := by
  ext n m : 1
  guard_target = n = m
  admit

section erasing_ext_attribute

def f (p : Int × Int) : Int × Int := (p.2, p.1)

example : f ∘ f = id := by
  ext ⟨a, b⟩
  · simp [f]
  · simp [f]

attribute [-ext] Prod.ext

example : f ∘ f = id := by
  ext ⟨a, b⟩
  simp [f]

end erasing_ext_attribute

/-!
Generating ext_iff lemma
-/
structure MyFun (α β : Type _) where
  toFun : α → β

@[ext]
theorem MyFun.ext {α β : Type _} (x y : MyFun α β) (h : ∀ a, x.toFun a = y.toFun a) : x = y := by
  cases x; cases y; simp; funext; apply h

/--
info: MyFun.ext_iff.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : MyFun α β} : x = y ↔ ∀ (a : α), x.toFun a = y.toFun a
-/
#guard_msgs in #check MyFun.ext_iff


/-!
Preserving inst implicits in ext_iff theorem
-/
section
attribute [local ext] Subsingleton.elim
/-- info: Subsingleton.elim_iff.{u} {α : Sort u} [h : Subsingleton α] {a b : α} : a = b ↔ True -/
#guard_msgs in #check Subsingleton.elim_iff
end


/-!
More informative error (issue #4758)
-/

/--
error: Failed to generate an 'ext_iff' theorem from 'weird_prod_ext': argument f is not a proof, which is not supported for arguments after p and q

Try '@[ext (iff := false)]' to prevent generating an 'ext_iff' theorem.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
@[ext]
theorem weird_prod_ext (p q : α × β)
    (f : α → α') (g : β → β') -- (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f p.1 = f q.1) (h' : g p.2 = g q.2) :
  p = q := sorry

/--
error: Failed to generate an 'ext_iff' theorem from 'ext'': argument h1 is depended upon, which is not supported for arguments after p and q

Try '@[ext (iff := false)]' to prevent generating an 'ext_iff' theorem.
-/
#guard_msgs in
@[ext]
theorem Sigma.ext' {β : α → Type _} (p q : (i : α) × β i)
    (h1 : p.1 = q.1)
    (h2 : h1 ▸ p.2 = q.2) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl
