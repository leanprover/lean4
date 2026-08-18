/-!
# Testing "go to definition" for `structure`
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
"Go to definition" for the structure itself
-/
example := S
         --^ textDocument/definition

/-!
"Go to definition" for a field
-/
example (s : S) := s.b
                   --^ textDocument/definition
