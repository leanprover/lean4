import Lean

register_option myBoolOpt : Bool := {
  defValue := false
  descr    := "my Boolean option"
}

register_option myNatOpt : Nat := {
  defValue := 100
  descr    := "my Nat option"
}
