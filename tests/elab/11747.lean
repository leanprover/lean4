module

/-! `ext_iff.2` used to fail because `getFunInfo` was operating in the public scope. -/

public structure A where
  private a : Nat

theorem ext_iff {x y : A} : x = y ↔ x.a = y.a := by
  rw [A.mk.injEq]

theorem ext {x y : A} : x.a = y.a → x = y := by
  exact ext_iff.2
