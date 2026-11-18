module

/-!
Input for `run_test.sh`: declarations whose `.olean` output used to depend on `Elab.async`.
-/

public def f (n : Nat) (_h : n > 0) : Nat := n

-- realizes `f.congr_simp` inside the proof
public theorem foo (a : Nat) (h : a + 0 > 0) : f (a + 0) h = f a (by simpa using h) := by
  simp

-- creates auxiliary theorems and records an extra module use inside each proof; `h` is used only
-- implicitly, so the `unusedVariables` linter must see the proof's info trees
public theorem bar (a b : Nat) (h : a < b) : a + 1 ≤ b ∧ a ≠ b := by
  constructor <;> omega

public theorem baz (a b : Nat) (h : a < b) : a + 1 ≤ b ∧ a ≠ b := by
  constructor <;> omega

-- the forward reference is stored as a deferred check together with the current options
set_option doc.verso true in
/-- See {name (scope := "OleanAsync")}`later`. -/
public def early : Nat := 1

public def later : Nat := 2

private theorem priv : 0 = 0 := rfl

public def g (n : Nat) : Nat :=
  if n = 0 then 1 else n * g (n - 1)

public theorem g_pos (n : Nat) : 0 < g n := by
  induction n with
  | zero => simp [g]
  | succ n ih => rw [g]; simp; exact ih
