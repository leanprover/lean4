axiom appendNil {α} (as : List α) : as ++ [] = as
axiom appendAssoc {α} (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs)
axiom reverseEq {α} (as : List α) : as.reverse.reverse = as

theorem ex1 {α} (as bs : List α) : as.reverse.reverse ++ [] ++ [] ++ bs ++ bs = as ++ (bs ++ bs) := by
  rw [appendNil, appendNil, reverseEq];
  traceState;
  rw [←appendAssoc];


theorem ex2 {α} (as bs : List α) : as.reverse.reverse ++ [] ++ [] ++ bs ++ bs = as ++ (bs ++ bs) := by
rewrite [reverseEq, reverseEq]; -- Error on second reverseEq
done

axiom zeroAdd (x : Nat) : 0 + x = x

theorem ex2 (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [zeroAdd] at h₁ h₂;
traceState;
subst x;
subst y;
exact rfl

theorem ex3 (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [zeroAdd] at *;
subst x;
subst y;
exact rfl

theorem ex4 (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [appendAssoc] at *; -- Error
done

theorem ex5 (m n k : Nat) (h : 0 + n = m) (h : k = m) : k = n := by
rw [zeroAdd] at *;
traceState; -- `h` is still a name for `h : k = m`
refine Eq.trans h ?hole;
apply Eq.symm;
assumption

theorem ex6 (p q r : Prop) (h₁ : q → r) (h₂ : p ↔ q) (h₃ : p) : r := by
rw [←h₂] at h₁;
exact h₁ h₃

theorem ex7 (p q r : Prop) (h₁ : q → r) (h₂ : p ↔ q) (h₃ : p) : r := by
rw [h₂] at h₃;
exact h₁ h₃
