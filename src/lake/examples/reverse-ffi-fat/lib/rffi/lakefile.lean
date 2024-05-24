import Lake
open System Lake DSL

package rffi

require dep from ".."/"dep"

@[default_target]
lean_lib RFFI where
  defaultFacets := #[LeanLib.staticFatFacet]
  -- NOTE: do *not* do what is below, it will build a libRFFI.a that
  -- does not include `Dep`.
  -- defaultFacets := #[LeanLib.staticFacet]
