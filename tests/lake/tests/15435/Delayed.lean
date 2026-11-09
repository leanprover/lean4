module

/-! # Plugin facet of a running target (#15435)

This library loads `delayed:shared` as a plugin. The job of the custom target `delayed` has not
finished when Lake fetches the plugin.
-/
