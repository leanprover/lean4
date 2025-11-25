import Lake
open System Lake DSL

package rffi

@[default_target]
lean_lib RFFI where
  defaultFacets := #[LeanLib.sharedFacet]
