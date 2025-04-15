/-
# Testing monad lift coercion elaborator

The functions inserted for the coercions are supposed to be inlined immediately during elaboration.
-/

set_option pp.mvars false

variable (p : Nat → Prop) (m : IO (Subtype p))

/-!
`Lean.Internal.liftCoeM`
-/
#check (m : (ReaderT Int IO) Nat)

/-!
`Lean.Internal.coeM`
-/
#check (m : IO Nat)

/-!
Making sure the monad lift coercion elaborator does not have side effects.

It used to be responsible for hinting that the LHSs of equalities were defeq, like in the following example.
It was checking that `Eq (some true)` and `Eq _` were defeq monads. The defeq check caused `_` to be solved as `some true`.
-/
/--
error: invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  ?_
-/
#guard_msgs in
example : some true = (some true).map id := by
  refine show _ = .some true from ?_
  rfl
