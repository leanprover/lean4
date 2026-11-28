module

public meta import DerivingTest.TestHandlers
import all DerivingTest.Handlers -- for `Secret` type class

/-!
In a `meta` section, we generate `meta` instances; this is particularly relevant for
`meta import`ed declarations.
-/

public meta section

open Lean Meta Deriving

deriving instance AllGeneralClasses, OtherDataClasses, OtherLawClasses for
  Lean.Meta.Deriving.ExprPair

/-- info: @[instance_reducible, expose] meta def instToDataExprPair : ToData ExprPair -/
#guard_msgs in
#print sig instToDataExprPair

end
