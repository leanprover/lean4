/-!
Tests the type correctness check of the motive in `rw`, which only checks the subterms containing the
abstracted occurrences, and falls back to `Meta.check` for binders whose type or value is rewritten.
-/

-- Occurrences in applications, lambdas, foralls, lets, and projections.
example (a b : Nat) (f : Nat → Nat) (h : a = b) :
    (fun x => f x + a) = (fun x => f x + b) := by
  rw [h]

example (a b : Nat) (p : Nat → Nat → Prop) (h : a = b) (hp : ∀ x, p x b) : ∀ x, p x a := by
  rw [h]; exact hp

example (a b : Nat) (h : a = b) : (let x := 1; x + a) = (let x := 1; x + b) := by
  rw [h]

example (a b : Nat) (h : a = b) : (a, 1).1 = b := by
  rw [h]

-- Dependent arguments after the rewritten one.
example (n m : Nat) (h : n = m) (f : (k : Nat) → Fin (k + 1)) : (f n).val ≤ n := by
  rw [h]
  exact Nat.lt_succ_iff.mp (f m).isLt

-- Sequences of binders.
example (a b : Nat) (h : a = b) : (fun (x y : Nat) => let z := x; z + y + a) = (fun x y => x + y + b) := by
  rw [h]

example (a b : Nat) (p : Nat → Nat → Nat → Prop) (h : a = b) (hp : ∀ x y, let z := y; p x z b) :
    ∀ x y, let z := y; p x z a := by
  rw [h]; exact hp

example (a b : Nat) (p : Nat → Nat → Prop) (h : a = b) :
    (fun x => ∀ y, p x (y + a)) = (fun x => ∀ y, p x (y + b)) := by
  rw [h]

-- Function types that need to be unfolded between arguments.
def Fn3 (α : Type) := α → α → α → α

example (a b : Nat) (h : a = b) (f : Nat → Fn3 Nat) (hf : f 0 b 1 2 = 0) : f 0 a 1 2 = 0 := by
  rw [h]; exact hf

example (a b : Nat) (h : a = b) (f : Fn3 Nat) (hf : f 1 2 b = 0) : f 1 2 a = 0 := by
  rw [h]; exact hf

-- `Meta.check` is only used for occurrences in binder types and let values.
#guard_msgs in
set_option trace.Meta.check true in
example (a b : Nat) (h : a = b) (f : Nat → Fn3 Nat) (hf : f 0 b 1 2 = 0) : f 0 a 1 2 = 0 := by
  rw [h]; exact hf

/-- trace: [Meta.check] ✅️ fun _a => ∀ (x : Fin _a), ↑x < _a -/
#guard_msgs in
set_option trace.Meta.check true in
example (a b : Nat) (h : a = b) (hp : ∀ x : Fin b, x.val < b) : ∀ x : Fin a, x.val < a := by
  rw [h]; exact hp

example (a b : Nat) (h : a = b) : (let x := a; x) = b := by
  rw [h]

-- The motive is still rejected when it is not type correct.
/--
error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => (fun k x => True) _a v
Error: Application type mismatch: The argument
  v
has type
  Fin n
but is expected to have type
  Fin _a
in the application
  (fun k x => True) _a v

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

n m : Nat
h : n = m
v : Fin n
⊢ (fun k x => True) n v
-/
#guard_msgs in
example (n m : Nat) (h : n = m) (v : Fin n) : (fun (k : Nat) (_ : Fin k) => True) n v := by
  rw [h]
