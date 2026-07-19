module

public import Linters

public def shouldBeFlaggedDummyMarker : Nat := 1

private def shouldNotBeFlaggedPrivateDummyMarker : Nat := 2

public def publicUnusedVarFixture : Nat :=
  let publicUnusedLet := 5
  3

private def privateUnusedVarFixture : Nat :=
  let privateUnusedLet := 7
  3
