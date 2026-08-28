/-!
Tests that the `internalModule` linter also fires in submodules of a module matching
`internalModulePrefixes` (here the test-only prefix `IMLinterTest`).
-/

-- warns: non-internal declaration in a submodule of an internal module
def subLeaky := 5
