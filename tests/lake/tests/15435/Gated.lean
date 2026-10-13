module

/-! # Plugin facet of a package (#15435)

This library loads `Lib:gated` as a plugin. The fetch function of the package's own facet `gated`
waits for a promise.
-/
