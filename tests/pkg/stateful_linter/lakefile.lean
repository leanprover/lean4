import Lake
open System Lake DSL

package stateful_linter

-- Default (async) library: async reader test, mode-switch and error tests (which toggle mode
-- per-command), plus the shared linter modules.
@[default_target]
lean_lib LinterTest

-- Synchronous library: a single file whose whole-file `Elab.async false` comes from `leanOptions`
-- here, so no in-file `set_option` command is counted/leaked by the linters.
@[default_target]
lean_lib LinterTestSync where
  leanOptions := #[⟨`Elab.async, false⟩]
