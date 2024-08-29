/-!
Test that `..` tokens do not break nearby `.`s.

Note that this tests specifically for issues with `.` that are not present with `·`.
-/

example : True ∧ True := by
  constructor
  refine trivial ..
  . trivial -- this has to be . not · for this test to be useful
