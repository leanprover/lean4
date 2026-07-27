set_option linter.defProp true

def shouldBeTheoremInSub : 1 = 1 := rfl

def unusedVarInSub : Nat :=
  let unusedInSub := 7
  3

def undocumentedInSub : Nat := 99
