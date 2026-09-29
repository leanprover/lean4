import Lake
open System Lake DSL

package collectAxioms
@[default_target] lean_lib CollectAxioms
@[default_target] lean_lib Untracked where
  roots := #[`Untracked.Base]
  leanOptions := #[⟨`trackAxioms, false⟩]
