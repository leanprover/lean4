/-!
Tests that `induction` accepts targets whose indices are structure constructor applications
`⟨x₁, …, xₙ⟩` or projections `x.f` of variables. Such an index is turned into a fresh variable by
the definitional change of variables `xᵢ ↦ y.fᵢ` resp. `x ↦ ⟨y₁, …, yₙ⟩`, so no equations are
introduced and the inductive hypotheses stay clean.
-/

structure Wrap where
  inner : Nat

/--
trace: case single
a : Nat
b b✝ : Wrap
hr : { inner := a } = b✝
⊢ a = b✝.inner
---
trace: case tail
a : Nat
b b✝ c✝ : Wrap
h : Relation.TransGen (fun a b => a = b) { inner := a } b✝
hr : b✝ = c✝
ih : a = b✝.inner
⊢ a = c✝.inner
-/
#guard_msgs in
example {a b} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a = b := by
  induction h with
  | single hr => trace_state; grind
  | tail h hr ih => trace_state; grind

example {a b} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a = b := by
  induction h
  case single => grind
  case tail => grind

-- Projection direction: the index `x.inner` becomes a variable and `x` becomes `⟨x⟩`.
/--
trace: case single
a x b✝ : Nat
hr : a = b✝
⊢ a = b✝
---
trace: case tail
a x b✝ c✝ : Nat
h : Relation.TransGen (fun a b => a = b) a b✝
hr : b✝ = c✝
ih : a = b✝
⊢ a = c✝
-/
#guard_msgs in
example {a : Nat} {x : Wrap} (h : Relation.TransGen (fun a b : Nat => a = b) a x.inner) :
    a = x.inner := by
  induction h with
  | single hr => trace_state; grind
  | tail h hr ih => trace_state; grind

-- Hypotheses depending on the replaced variable are rewritten too.
example {a b} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) (hb : 0 < b) :
    0 < a := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

-- Chains of constructors.
structure Wrap2 where
  w : Wrap

example {a b} (h : Relation.TransGen (fun a b : Wrap2 => a = b) ⟨.mk a⟩ ⟨.mk b⟩) : a = b := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

-- Chains of projections.
example {a : Nat} {x : Wrap2} (h : Relation.TransGen (fun a b : Nat => a = b) a x.w.inner) :
    a = x.w.inner := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

-- Projection of a multi-field structure: the other fields become inaccessible variables.
/--
trace: case single
a p snd✝ : Nat
hp : snd✝ = 3
b✝ : Nat
hr : a = b✝
⊢ a = b✝
---
trace: case tail
a p snd✝ : Nat
hp : snd✝ = 3
b✝ c✝ : Nat
h : Relation.TransGen (fun a b => a = b) a b✝
hr : b✝ = c✝
ih : a = b✝
⊢ a = c✝
-/
#guard_msgs in
example {a : Nat} {p : Nat × Nat} (hp : p.2 = 3)
    (h : Relation.TransGen (fun a b : Nat => a = b) a p.1) : a = p.1 := by
  induction h with
  | single hr => trace_state; grind
  | tail h hr ih => trace_state; grind

-- Multi-field and dependent structures.
example {a b c d : Nat} (h : Relation.TransGen (fun a b : Nat × Nat => a = b) (a, b) (c, d)) :
    a + b = c + d := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

example {a : Nat} {b : Fin a} {c : Nat} {d : Fin c}
    (h : Relation.TransGen (fun a b : (n : Nat) × Fin n => a = b) ⟨a, b⟩ ⟨c, d⟩) :
    a = c := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

-- Several indices at once.
inductive Le : Wrap → Wrap → Prop
  | zero (b) : Le ⟨0⟩ b
  | succ (a b) : Le a b → Le ⟨a.inner + 1⟩ ⟨b.inner + 1⟩

example {a b : Nat} (h : Le ⟨a⟩ ⟨b⟩) : a ≤ b := by
  induction h with
  | zero => exact Nat.zero_le _
  | succ _ _ _ ih => exact Nat.succ_le_succ ih

-- `generalizing` still works on the remaining variables.
example {a b c : Nat} (h : Le ⟨a⟩ ⟨b⟩) (hc : c ≤ a) : c ≤ b := by
  induction h generalizing c with
  | zero => exact Nat.le_trans hc (Nat.zero_le _)
  | succ _ _ _ ih => exact Nat.le_trans hc (Nat.succ_le_succ (ih (Nat.le_refl _)))

-- Let-bound hypotheses depending on the replaced variable are reverted and reintroduced.
example {a b} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a ≤ b := by
  let c := b + 1
  have hc : a < c → a ≤ b := Nat.le_of_lt_succ
  induction h with
  | single hr => exact hc (by grind)
  | tail h hr ih => exact hc (by grind)

-- Indices that are not built from variables by constructors and projections are still rejected.
/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  { inner := 0 }
-/
#guard_msgs in
example {a : Nat} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk 0)) : a = 0 := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  { inner := a + 1 }
-/
#guard_msgs in
example {a : Nat} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk (a + 1))) :
    False := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

-- The index is only visible after unfolding the target's type: `H x y` unfolds to `P x.as y.as`.
structure W where
  as : Nat

inductive P : Nat → Nat → Prop
  | refl (a) : P a a
  | step (a b) : P a b → P a (b + 1)

def H (a b : W) : Prop := P a.as b.as

/--
trace: case refl
x : W
y : Nat
⊢ x.as ≤ x.as
---
trace: case step
x : W
y b✝ : Nat
a✝ : P x.as b✝
ih : x.as ≤ b✝
⊢ x.as ≤ b✝ + 1
-/
#guard_msgs in
example {x y : W} (h : H x y) : x.as ≤ y.as := by
  induction h with
  | refl => trace_state; exact Nat.le_refl _
  | step _ _ ih => trace_state; exact Nat.le_succ_of_le ih

-- Proof fields are irrelevant when folding `⟨y.val, h⟩` back into `y`.
inductive Pos : {n : Nat // 0 < n} → Prop
  | one : Pos ⟨1, Nat.one_pos⟩
  | succ (p) : Pos p → Pos ⟨p.val + 1, Nat.succ_pos _⟩

/--
trace: case one
x✝ : { n // 0 < n }
hq : 0 < ⟨1, Nat.one_pos⟩.val
h' : ⟨1, Nat.one_pos⟩.val = ⟨1, Nat.one_pos⟩.val
⊢ 1 ≤ ⟨1, Nat.one_pos⟩.val
---
trace: case succ
x✝ p : { n // 0 < n }
a✝ : Pos p
ih : 0 < p.val → p.val = p.val → 1 ≤ p.val
hq : 0 < ⟨p.val + 1, ⋯⟩.val
h' : ⟨p.val + 1, ⋯⟩.val = ⟨p.val + 1, ⋯⟩.val
⊢ 1 ≤ ⟨p.val + 1, ⋯⟩.val
-/
#guard_msgs in
example {a : Nat} (hp hq : 0 < a) (h : Pos ⟨a, hp⟩) (h' : (⟨a, hq⟩ : {n // 0 < n}).val = a) :
    1 ≤ a := by
  induction h with
  | one => trace_state; exact Nat.le_refl _
  | succ p _ ih => trace_state; exact Nat.le_add_right_of_le (ih p.2 rfl)

-- Inside a section, the auxiliary declaration for the recursive reference (`_example`, `sec`) mentions
-- the section variables, so the change of variables has to deal with it.
section
variable {a b : Nat}

example (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a = b := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

theorem sec (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a = b := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind
end

-- A let-bound base variable is kept in the context as a definition while its occurrences are
-- replaced; the new variable takes its place as the index.
/--
trace: case single
b : Nat := 3
b✝ : Wrap
hr : { inner := 3 } = b✝
⊢ True
-/
#guard_msgs in
example : True := by
  let b := 3
  have h : Relation.TransGen (fun a b : Wrap => a = b) (.mk 3) (.mk b) := .single rfl
  induction h with
  | single hr => trace_state; trivial
  | tail _ _ _ => trivial

-- The new variable is named like the let-bound base it replaces. Normally `induction` clears it in
-- the alternatives, but an instance-implicit hypothesis depending on it is not generalized (as for
-- any index variable), so the variable stays and shadows the definition.
/--
trace: case single
b✝¹ : Nat := 3
b : Nat
inst : Decidable (b = 3)
b✝ : Wrap
hr : { inner := 3 } = b✝
⊢ True
-/
#guard_msgs in
example : True := by
  let b := 3
  have h : Relation.TransGen (fun a b : Wrap => a = b) (.mk 3) (.mk b) := .single rfl
  have aux : ∀ [Decidable (b = 3)], True := by
    intro inst
    induction h with
    | single hr => trace_state; trivial
    | tail _ _ _ => trivial
  exact aux
