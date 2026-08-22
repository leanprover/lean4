/-!
# Testing "go to definition" for `structure` fields
-/

--^ collectDiagnostics

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

/-!
The field terminfo is still available even if there is an exception during elaboration.
Field redeclaration currently throws an exception, preventing the step where the projection
terminfos are added (and preventing adding the structure to the environment).
-/
structure SInvalid where
  a : Nat
--^ textDocument/hover
  a : Nat

-- Check that the structure is never added to the environment:
#check SInvalid
