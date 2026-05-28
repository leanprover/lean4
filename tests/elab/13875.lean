/-!
Regression test for https://github.com/leanprover/lean4/issues/13785.
-/

example (s : String) (x : Nat) : String :=
  let := s.all (·.isAlphanum)
  match x with
  | _ => s
