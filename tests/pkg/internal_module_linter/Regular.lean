/-!
Tests that the `internalModule` linter stays silent in a module that is not internal, even with
the linter enabled.
-/

-- no warning: `Regular` is not an internal module
def regularDef := 7
