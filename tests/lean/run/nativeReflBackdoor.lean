--

/-
This example demonstratea that when we are using `native_decide`,
we are also trusting the correctness of `implemented_by` annotations,
foreign functions (i.e., `[extern]` annotations), etc.
-/
def g (b : Bool) := false

/-
The following `implemented_by` is telling the compiler
"trust me, `g` does implement `f`"
which is clearly false in this example.
-/
@[implemented_by g]
def f (b : Bool) := b

theorem fConst (b : Bool) : f b = false :=
match b with
| true  =>
  /- The following `native_decide` is going to use `g` to evaluate `f`
     because of the `implemented_by` directive. -/
  have : (f true) = false := by native_decide
  this
| false => rfl

theorem trueEqFalse : true = false :=
have h₁ : f true = true  := rfl;
have h₂ : f true = false := fConst true;
Eq.trans h₁.symm h₂

/-
We managed to prove `False` using the unsound annotation `implemented_by` above.
-/
theorem unsound : False :=
Bool.noConfusion trueEqFalse

#print axioms unsound -- axiom 'Lean.ofReduceBool' is listed
