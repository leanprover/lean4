/-!
Tests that the `internalModule` linter considers a module internal when `Internal` is one of its
name components, independently of `internalModulePrefixes`.
-/

-- warns: non-internal declaration in a module with an `Internal` name component
def helpersLeaky := 8
