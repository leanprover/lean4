/-!
# Ensure autoparam errors are placed at elaboration position

Before, errors were placed at the beginning of the file.
-/


/-!
Testing `infer_instance`, which defers a typeclass problem beyond the tactic script execution.
-/
class A

-- For structure instance elaboration ...
structure B where
  h1 : A := by infer_instance

example : B where
          --^ collectDiagnostics

-- ... and for app elaboration.
def baz (_h1 : A := by infer_instance) : Nat := 1

example : Nat := baz
               --^ collectDiagnostics


/-!
Testing a tactic that immediately throws an error, but incrementality resets the ref
from the syntax for the tactic (which would be a `.missing` position for autoparams).
-/

structure B' where
  h1 : A := by done

example : B' where
           --^ collectDiagnostics
