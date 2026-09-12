/-!
Tests that `induction` accepts indices built from variables by constructors and projections
of one-field structures. The tactic replaces an index `⟨x⟩` with a fresh variable `y` by
substituting `y.f` for `x`. For an index `x.f`, it substitutes `⟨y⟩` for `x`.
These changes are definitional, so they introduce no equations into the induction hypotheses.
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

-- Annotations around an index, its base variable, or an intermediate projection must not prevent folding.
example {a b : Nat}
    (h : Relation.TransGen (fun a b : Wrap => a = b) ⟨a⟩ (no_index (Wrap.mk b))) : a = b := by
  induction h <;> grind

example {a b : Nat}
    (h : Relation.TransGen (fun a b : Wrap => a = b) ⟨a⟩ ⟨no_index b⟩) : a = b := by
  induction h <;> grind

example {a : Nat} {x : Wrap}
    (h : Relation.TransGen (fun a b : Wrap => a = b) ⟨a⟩ ⟨no_index x.inner⟩) : a = x.inner := by
  induction h <;> grind

example {a : Nat} {x : Wrap}
    (h : Relation.TransGen (fun a b : Nat => a = b) a (no_index x.inner)) : a = x.inner := by
  induction h <;> grind

example {a : Nat} {x : Wrap}
    (h : Relation.TransGen (fun a b : Nat => a = b) a (no_index x).inner) : a = x.inner := by
  induction h <;> grind

example {a : Nat} {x : Wrap2}
    (h : Relation.TransGen (fun a b : Nat => a = b) a
      (no_index (no_index (no_index x).w).inner)) : a = x.w.inner := by
  induction h <;> grind

-- Only one-field structures are supported.
/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  (c, d)
-/
#guard_msgs in
example {a b c d : Nat} (h : Relation.TransGen (fun a b : Nat × Nat => a = b) (a, b) (c, d)) :
    a + b = c + d := by
  induction h with
  | single hr => grind
  | tail h hr ih => grind

/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  p.fst
-/
#guard_msgs in
example {a : Nat} {p : Nat × Nat} (h : Relation.TransGen (fun a b : Nat => a = b) a p.1) :
    a = p.1 := by
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

-- Dependent indices: reparametrizing `n` reintroduces `i` with a new type and free variable ID.
-- The second reparametrization must use the reintroduced `i`.
structure FinWrap (n : Nat) where
  inner : Fin (n + 1)

inductive IsZero : (n : Wrap) → FinWrap n.inner → Prop
  | zero (n) : IsZero n ⟨0⟩
  | succ {n i} : IsZero n i → IsZero ⟨n.inner + 1⟩ ⟨i.inner.castSucc⟩

example (n : Nat) (i : Fin (n + 1)) (h : IsZero ⟨n⟩ ⟨i⟩) : i.val = 0 := by
  induction h with
  | zero => rfl
  | succ _ ih => exact ih

-- A constructor/projection chain can reintroduce the dependent base more than once.
example (n : Wrap) (i : Fin (n.inner + 1)) (h : IsZero ⟨n.inner⟩ ⟨i⟩) : i.val = 0 := by
  induction h with
  | zero => rfl
  | succ _ ih => exact ih

-- Generalizing the explicit targets creates a fresh variable that also becomes an implicit index.
-- The duplicate-target diagnostic must use its display name from the updated goal's context.
theorem Le.ind {motive : (a b : Wrap) → Le a b → Prop}
    (all : ∀ a b h, motive a b h) (a : Wrap) {b : Wrap} (h : Le a b) : motive a b h :=
  all a b h

/--
error: Invalid target: The variable `x✝¹` occurs in more than one target (or index), consider using the `cases` tactic instead
  x✝¹
  x✝¹
-/
#guard_msgs in
example (a : Nat) (h : Le ⟨a⟩ ⟨a⟩) : True := by
  induction Wrap.mk a, (id h) using Le.ind

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

-- A subtype has two fields, even though the second one is a proof.
inductive Pos : {n : Nat // 0 < n} → Prop
  | one : Pos ⟨1, Nat.one_pos⟩
  | succ (p) : Pos p → Pos ⟨p.val + 1, Nat.succ_pos _⟩

/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  ⟨a, hp⟩
-/
#guard_msgs in
example {a : Nat} (hp : 0 < a) (h : Pos ⟨a, hp⟩) : 1 ≤ a := by
  induction h with
  | one => exact Nat.le_refl _
  | succ p _ ih => exact Nat.le_add_right_of_le (ih p.2)

-- The type of the new variable must not depend on the base, neither directly nor through a
-- let-bound definition. Then the outer step is skipped and the index is rejected as usual.
structure Outer (p : Prop) (h : p) where
  inner : Wrap

example {a : Nat} (p : Prop) (hp : p) (o : Outer p hp)
    (hr : Relation.TransGen (fun x y : Outer p hp => x = y) o ⟨⟨a⟩⟩) : True := by
  induction hr with
  | single _ => trivial
  | tail _ _ _ => trivial

/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  { inner := a }
-/
#guard_msgs in
example {a : Nat} (ha : 0 < a) (o : Outer (0 < a) ha)
    (hr : Relation.TransGen (fun x y : Outer (0 < a) ha => x = y) o ⟨⟨a⟩⟩) : True := by
  induction hr with
  | single _ => trivial
  | tail _ _ _ => trivial

/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  { inner := a }
-/
#guard_msgs in
example {a : Nat} (ha : 0 < a) : True := by
  let c := a
  have h : 0 < c := ha
  have r : ∀ o : Outer (0 < c) h, Relation.TransGen (fun x y : Outer (0 < c) h => x = y) o ⟨⟨a⟩⟩ → True := by
    intro o hr
    induction hr with
    | single _ => trivial
    | tail _ _ _ => trivial
  trivial

-- A metavariable in the goal whose context contains the base becomes a function of the new variable,
-- like `revert` does. Here `?n` is created before the target exists…
/--
trace: case single
o a b✝ : Wrap
a✝ : o = b✝
⊢ ?_ = b✝.inner
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option pp.mvars false in
example {a : Nat} {o : Wrap} : ∃ n, n = a := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    have h : Relation.TransGen (fun x y : Wrap => x = y) o ⟨a⟩ := .single sorry
    induction h with
    | single _ => trace_state; sorry
    | tail _ _ _ => sorry
  exact a

-- … and here after, so that the reverted target is in its context as well.
/--
trace: case single
o a b✝ : Wrap
a✝ : o = b✝
⊢ ?_ ⋯ = b✝.inner
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option pp.mvars false in
example {a : Nat} {o : Wrap} (h : Relation.TransGen (fun x y : Wrap => x = y) o ⟨a⟩) :
    ∃ n, n = a := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    induction h with
    | single _ => trace_state; sorry
    | tail _ _ _ => sorry
  exact a

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
-- replaced. The new variable is named like the base; as index variables are not cleared by
-- `induction`, it shadows the definition in the alternatives.
/--
trace: case single
b✝¹ : Nat := 3
b b✝ : Wrap
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

-- Instance-implicit hypotheses depending on the base are transported like any other hypothesis.
/--
trace: case single
b✝¹ : Nat := 3
b : Wrap
inst : Decidable (b.inner = 3)
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
