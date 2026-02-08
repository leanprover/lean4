/-!
# Improve compiler IR check message for users when constants are not compiled
-/

/-
This is a simplified version of the example in #1785.
Note that the error changes if the typeclass argument is removed.
-/

noncomputable
def char (R : Type) [∀ n, OfNat R n] : Nat := 0

/--
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'char', which is 'noncomputable'
-/
#guard_msgs in
def bug (R : Type) [∀ n, OfNat R n] : R :=
  match char R with
  | 0 => 1
  | _ => 0
