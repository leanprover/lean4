/-!
Tests that the `internalModule` linter does not consider a module internal merely because its
name contains "Internal" as a substring; `Internal` must be a whole name component.
-/

-- no warning: `UsesInternalHelpers` is not an internal module
def substringLeaky := 7
