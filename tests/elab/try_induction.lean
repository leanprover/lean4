/-
Tests for `try?` suggesting `induction` tactic.

NOTE: Tests using Nat or List from the standard library don't work because
induction candidates are filtered by `isEligible` in Try/Collect.lean, which
only accepts types defined in the current module and/or namespace.
This is why we use custom inductive types below.

Real working examples from the library (like grind_hyper_ex.lean) use:
  `induction k with grind`
to prove things like `hyperoperation 1 m k = m + k`. However, `try?` won't
suggest these because `k : Nat`.
-/

-- Simple list-like structure
inductive MyList (α : Type _) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

axiom MyListProp : MyList α → Prop

@[grind .] axiom mylist_nil : MyListProp (MyList.nil : MyList α)
@[grind .] axiom mylist_cons : ∀ (x : α) (xs : MyList α), MyListProp xs → MyListProp (MyList.cons x xs)

/--
info: Try these:
  [apply] (induction xs) <;> grind
  [apply] (induction xs) <;> grind only [mylist_nil, mylist_cons]
  [apply] ·
    induction xs
    · grind => instantiate only [mylist_nil]
    · grind => instantiate only [mylist_cons]
-/
#guard_msgs (info) in
example (xs : MyList α) : MyListProp xs := by
  try?

-- Expression tree
inductive Expr where
  | const : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

axiom ExprProp : Expr → Prop

@[grind .] axiom expr_const : ∀ n, ExprProp (Expr.const n)
@[grind .] axiom expr_add : ∀ e1 e2, ExprProp e1 → ExprProp e2 → ExprProp (Expr.add e1 e2)
@[grind .] axiom expr_mul : ∀ e1 e2, ExprProp e1 → ExprProp e2 → ExprProp (Expr.mul e1 e2)

/--
info: Try these:
  [apply] (induction e) <;> grind
  [apply] (induction e) <;> grind only [expr_const, expr_add, expr_mul]
  [apply] ·
    induction e
    · grind => instantiate only [expr_const]
    · grind => instantiate only [expr_add]
    · grind => instantiate only [expr_mul]
-/
#guard_msgs (info) in
example (e : Expr) : ExprProp e := by
  try?

-- For now, `try?` will not do induction on `Nat`, so we use a custom Nat-like type.

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

abbrev ℕ := MyNat

def add : MyNat → MyNat → MyNat
  | .zero, n => n
  | .succ m, n => .succ (add m n)

/--
info: Try these:
  [apply] (induction n) <;> grind [= add]
  [apply] (induction n) <;> grind only [add]
  [apply] (induction n) <;> grind => instantiate only [add]
-/
#guard_msgs in
@[grind =]
theorem add_zero (n : ℕ) : add n .zero = n := by
  try?

/--
info: Try these:
  [apply] (fun_induction add) <;> grind [= add]
  [apply] (fun_induction add) <;> grind only [add]
  [apply] (fun_induction add) <;> grind => instantiate only [add]
-/
#guard_msgs in
@[grind =]
theorem add_succ (m n : ℕ) : add m (.succ n) = .succ (add m n) := by
  try?

def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | .zero, _, k => .succ k
  | .succ .zero, m, .zero => m
  | .succ (.succ .zero), _, .zero => .zero
  | .succ (.succ (.succ _)), _, .zero => .succ .zero
  | .succ n, m, .succ k => hyperoperation n m (hyperoperation (.succ n) m k)

attribute [local grind] hyperoperation add

/--
info: Try these:
  [apply] grind
  [apply] grind only [hyperoperation]
  [apply] grind => instantiate only [hyperoperation]
-/
#guard_msgs in
@[grind =]
theorem hyperoperation_zero (m k : ℕ) : hyperoperation .zero m k = .succ k := by
  try?

/--
info: Try these:
  [apply] grind
  [apply] grind only [hyperoperation]
  [apply] grind => instantiate only [hyperoperation]
-/
#guard_msgs in
@[grind =]
theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (.succ n) m (.succ k) = hyperoperation n m (hyperoperation (.succ n) m k) := by
  try?

/--
info: Try these:
  [apply] (induction k) <;> grind
  [apply] (induction k) <;> grind only [hyperoperation, = add_zero, = add_succ]
  [apply] ·
    induction k
    · grind => instantiate only [hyperoperation, = add_zero]
    ·
      grind =>
        instantiate only [hyperoperation, = add_succ]
        instantiate only [hyperoperation]
-/
#guard_msgs in
@[grind =]
theorem hyperoperation_one (m k : ℕ) : hyperoperation (.succ .zero) m k = add m k := by
  try?
