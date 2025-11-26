module

meta import Module.Basic

/-! Basic phase restriction tests. -/
/--
error: Invalid definition `nonMeta`, may not access declaration `f` imported as `meta`; consider adding `import Module.Basic`
-/
#guard_msgs in
def nonMeta := f

/-- error: Invalid `meta` definition `veryMeta`, `nonMeta` not marked `meta` -/
#guard_msgs in
meta def veryMeta := nonMeta

/--
error: Invalid public `meta` definition `pubMetaImp`, `pubMeta` is not accessible here; consider adding `public import Module.Basic`
-/
#guard_msgs in
public meta def pubMetaImp := pubMeta
