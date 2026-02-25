import Std
set_option cbv.warning false

-- Basic test: inverted cbv_eval attribute
-- The theorem `42 = myConst` with ← becomes `myConst = 42`
-- so cbv can rewrite `myConst` to `42`
@[cbv_opaque] def myConst : Nat := 42

@[cbv_eval ←] theorem myConst_eq : 42 = myConst := by rfl

example : myConst = 42 := by
  conv =>
    lhs
    cbv

-- Test with a function application on the RHS
def myAdd (a b : Nat) : Nat := a + b

@[cbv_opaque] def myAddAlias (a b : Nat) : Nat := myAdd a b

-- The theorem `myAdd a b = myAddAlias a b` with ← becomes `myAddAlias a b = myAdd a b`
-- so cbv can rewrite `myAddAlias a b` to `myAdd a b`, which it can then evaluate
@[cbv_eval ←] theorem myAddAlias_eq (a b : Nat) : myAdd a b = myAddAlias a b := by
  unfold myAddAlias; rfl

example : myAddAlias 2 3 = 5 := by
  conv =>
    lhs
    cbv

-- Test with <- syntax (alternative arrow)
@[cbv_opaque] def myConst2 : Nat := 100

@[cbv_eval <-] theorem myConst2_eq : 100 = myConst2 := by rfl

example : myConst2 = 100 := by
  conv =>
    lhs
    cbv

-- Test that non-inverted cbv_eval still works
@[cbv_opaque] def myConst3 : Nat := 7

@[cbv_eval] theorem myConst3_eq : myConst3 = 7 := by rfl

example : 7 = 7 := by
  conv =>
    lhs
    cbv

-- Test with the optional ident argument (backward compatibility)
@[cbv_opaque] def myFn (n : Nat) : Nat := n + 1

@[cbv_eval myFn] theorem myFn_zero : myFn 0 = 1 := by rfl

example : 1 = 1 := by
  conv =>
    lhs
    cbv
