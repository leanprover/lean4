/-!
# Testing "go to definition" for `structure` fields
-/

structure S where
  a : Nat
  /- Dependence in type -/
  b : Fin a
        --^ textDocument/definition
  /- Dependence in default value. -/
  c : Nat := a + b
           --^ textDocument/definition
               --^ textDocument/definition

/-!
"Go to definition" for a field
-/
example (s : S) := s.b
                   --^ textDocument/definition
