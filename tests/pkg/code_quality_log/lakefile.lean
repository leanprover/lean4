import Lake
open System Lake DSL

package code_quality_log

-- Default (async) library: the linter registration module plus the async capture test.
@[default_target]
lean_lib CQTest

-- Synchronous library: the same capture test with the whole file elaborated under
-- `Elab.async false` via `leanOptions`, exercising the non-async branch of `runLintersAsync`.
@[default_target]
lean_lib CQTestSync where
  leanOptions := #[⟨`Elab.async, false⟩]
