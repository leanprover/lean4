/-!
Tests that the statements of equation lemmas do not depend on the options where the equations are
first requested. Proofs elaborate in parallel, so such a dependency makes the statements depend on
which proof requests the equations first. Regression test for #15498.
-/

inductive Walk : Nat → Nat → Type where
  | nil : Walk u u
  | cons : Walk v w → Walk u w

def Walk.getVert : Walk u v → Nat → Nat
  | nil, _ => u
  | cons _, 0 => u
  | cons q, n + 1 => q.getVert n

theorem Walk.getVert_zero (p : Walk u v) : p.getVert 0 = u := by cases p <;> rfl

-- Splitting the overlapping `p, 0` alternative depends on `respectTransparency`.
set_option backward.isDefEq.respectTransparency.types false in
def Walk.drop1 (p : Walk u v) (n : Nat) : Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => (p.getVert_zero).symm ▸ p
  | .cons q, n + 1 => q.drop1 n

set_option backward.isDefEq.respectTransparency.types false in
def Walk.drop2 (p : Walk u v) (n : Nat) : Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => (p.getVert_zero).symm ▸ p
  | .cons q, n + 1 => q.drop2 n

/--
info: Walk.drop1.eq_2 {u v : Nat} (p : Walk u v) (x : v = u → p ≍ Walk.nil → False) : p.drop1 0 = ⋯ ▸ p
-/
#guard_msgs in
#check Walk.drop1.eq_2

/--
info: Walk.drop2.eq_2 {u v : Nat} (p : Walk u v) (x : v = u → p ≍ Walk.nil → False) : p.drop2 0 = ⋯ ▸ p
-/
#guard_msgs in
set_option backward.isDefEq.respectTransparency false in
#check Walk.drop2.eq_2
