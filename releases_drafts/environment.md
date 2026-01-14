**Breaking Changes**

* The functions `Lean.Environment.importModules` and `Lean.Environment.finalizeImport` have been extended with a new parameter `loadExts : Bool := false` that enables environment extension state loading.
  Their previous behavior corresponds to setting the flag to `true` but is only safe to do in combination with `enableInitializersExecution`; see also the `importModules` docstring.
  The new default value `false` ensures the functions can be used correctly multiple times within the same process when environment extension access is not needed.
  The wrapper function `Lean.Environment.withImportModules` now always calls `importModules` with `loadExts := false` as it is incompatible with extension loading.
