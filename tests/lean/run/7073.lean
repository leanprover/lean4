/-!
# Auxiliary declaration name resolution in tactic blocks

https://github.com/leanprover/lean4/issues/7073

It should be possible to refer to auxiliary declarations by partially- or fully-qualified names
in tactic blocks.
-/

theorem A : True ∧ True := by
  let rec B := trivial
  exact And.intro A.B A.C
where C := trivial

namespace M

theorem N : True ∧ True ∧ True :=
  let rec O := by exact M.N.P
  by exact ⟨N.O, M.N.O, N.P⟩
where P := trivial

theorem Q.R : Nat → True
  | 0 => trivial
  | 1 => by exact Q.R 0
  | n + 2 => by exact M.Q.R (n + 1)
