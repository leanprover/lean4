import Lean

open Lean

initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

initialize registerBuiltinAttribute {
  name := `testPred
  descr := "Dummy attribute for testing"
  add := fun declName _stx _kind => do
    logInfo s!"Applied @testPred to {declName}"
}
