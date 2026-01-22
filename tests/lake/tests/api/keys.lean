import Lake
open System Lake DSL

package test

/-! ## Test Key String Representations -/

/-- info: Lake.BuildKey.packageTarget Lean.Name.anonymous `foo -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "foo"

/-- error: ill-formed target: expected module name after '+' -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "+"

/-- info: Lake.BuildKey.module `mod -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "+mod"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.module `mod) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "+mod:facet"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.facet (Lake.BuildKey.module `mod) `f1) `f2 -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "+mod:f1:f2"

/-- info: Lake.BuildKey.package Lean.Name.anonymous -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@"

/-- info: Lake.BuildKey.package `pkg -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.package `pkg) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg:facet"

/-- info: Lake.BuildKey.packageTarget `pkg `tgt -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg/tgt"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageTarget `pkg `tgt) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg/tgt:facet"

/-- info: Lake.BuildKey.packageModule `pkg `mod -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg/+mod"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageModule `pkg `mod) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@pkg/+mod:facet"

/-- info: Lake.BuildKey.packageTarget Lean.Name.anonymous `tgt -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@/tgt"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageTarget Lean.Name.anonymous `tgt) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@/tgt:facet"

/-- info: Lake.BuildKey.packageModule Lean.Name.anonymous `mod -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@/+mod"

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageModule Lean.Name.anonymous `mod) `facet -/
#guard_msgs in #eval IO.ofExcept <| PartialBuildKey.parse "@/+mod:facet"

/-! ## Test Key Literal Representations -/

/-- info: Lake.BuildKey.module `mod -/
#guard_msgs in #eval `+mod

/-- info: Lake.BuildKey.facet (Lake.BuildKey.module `mod) `facet -/
#guard_msgs in #eval `+mod:facet

/-- info: Lake.BuildKey.facet (Lake.BuildKey.facet (Lake.BuildKey.module `mod) `f1) `f2 -/
#guard_msgs in #eval `+mod:f1:f2

/-- info: Lake.BuildKey.package Lean.Name.anonymous -/
#guard_msgs in #eval `@

/-- info: Lake.BuildKey.package `pkg -/
#guard_msgs in #eval `@pkg

/-- info: Lake.BuildKey.facet (Lake.BuildKey.package `pkg) `facet -/
#guard_msgs in #eval `@pkg:facet

/-- info: Lake.BuildKey.packageTarget `pkg `tgt -/
#guard_msgs in #eval `@pkg/tgt

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageTarget `pkg `tgt) `facet -/
#guard_msgs in #eval `@pkg/tgt:facet

/-- info: Lake.BuildKey.packageModule `pkg `mod -/
#guard_msgs in #eval `@pkg/+mod

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageModule `pkg `mod) `facet -/
#guard_msgs in #eval `@pkg/+mod:facet

/-- info: Lake.BuildKey.packageTarget Lean.Name.anonymous `tgt -/
#guard_msgs in #eval `@/tgt

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageTarget Lean.Name.anonymous `tgt) `facet -/
#guard_msgs in #eval `@/tgt:facet

/-- info: Lake.BuildKey.packageModule Lean.Name.anonymous `mod -/
#guard_msgs in #eval `@/+mod

/-- info: Lake.BuildKey.facet (Lake.BuildKey.packageModule Lean.Name.anonymous `mod) `facet -/
#guard_msgs in #eval `@/+mod:facet

/-! ## Other Tests -/

-- Test syntax does not conflict with a type ascription
def stx  := (`@pkg : PartialBuildKey)

-- Test coercion to a target
def coe : Array (Target Dynlib) := #[`@pkg/tgt:facet]
