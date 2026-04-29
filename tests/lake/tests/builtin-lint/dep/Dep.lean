-- A public def without a docstring. `linter.missingDocs` (defValue=false) only
-- fires when `linter.all=true` is injected during the build. This file lives in
-- a non-root package (`dep`), so the option override must be keyed by the
-- `dep` package's baseName for the warning to be captured.
def undocumentedInDep : Nat := 7
