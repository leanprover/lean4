import Lean.Expr
/-!
Testing the macro for `mkAppN f #[x1,...,xn]`
-/

open Lean

/-!
Checking the expansion with zero arguments.
The macro has an `Expr` type ascription to make this work.
-/
#check mkAppN (.const ``And []) #[]

/-!
Checking the macro expansion with more than one argument.
-/
#check mkAppN (.const ``And []) #[.const ``True [], .const ``False []]

/-!
Checking the macro expansion with more than one argument.
(Using `==` to verify the previous test.)
-/
def e : Expr := .app (.app (.const ``And []) (.const ``True [])) (.const ``False [])

def e' : Expr := mkAppN (.const ``And []) #[.const ``True [], .const ``False []]

#eval e == e'

/-!
Make sure that `mkAppN` can be used in a pattern.
-/
#eval match e with | mkAppN f #[x, y] => some (f, x, y) | _ => none

/-!
Make sure that the expansion can handle `·`'s.
-/
#check (mkAppN · #[·])

/-!
Checking that the evaluation order for the `mkAppN` expansion is reasonable.
-/
def orderTest (f x y : Expr) : StateM String Expr := do
  let push (s : String) (e : Expr) : StateM String Expr := do
    modify (fun st => st ++ s)
    return e
  return mkAppN (← push "1" f) #[← push "2" x, ← push "3" y]

#eval (orderTest (.const ``And []) (.const ``True []) (.const ``False [])).run ""
