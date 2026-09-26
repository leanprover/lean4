import Lake
open Lake DSL

package wrappedExecManifest

lean_lib Dep

lean_lib Postponed where
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib Onlymod
