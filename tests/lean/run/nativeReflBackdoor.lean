--

/-
This example demonstratea that when we are using `nativeDecide`,
we are also trusting the correctness of `implementedBy` annotations,
foreign functions (i.e., `[extern]` annotations), etc.
-/
def g (b : Bool) := false

/-
The following `implementedBy` is telling the compiler
"trust me, `g` does implement `f`"
which is clearly false in this example.
-/
@[implementedBy g]
def f (b : Bool) := b

theorem fConst (b : Bool) : f b = false :=
match b with
| true  =>
  /- The following `nativeDecide` is going to use `g` to evaluate `f`
     because of the `implementedBy` directive. -/
  have : (f true) = false := by nativeDecide
  this
| false => rfl

theorem trueEqFalse : true = false :=
have h₁ : f true = true  := rfl;
have h₂ : f true = false := fConst true;
Eq.trans h₁.symm h₂

/-
We managed to prove `False` using the unsound annotation `implementedBy` above.
-/
theorem unsound : False :=
Bool.noConfusion trueEqFalse

#print axioms unsound -- axiom 'Lean.ofReduceBool' is listed
