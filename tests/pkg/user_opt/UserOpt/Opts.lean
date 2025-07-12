import Lean

register_option myBoolOpt : Bool := {
  defValue := false
  descr    := "my Boolean option"
}

register_option myNatOpt : Nat := {
  defValue := 100
  descr    := "my Nat option"
}

register_option myDeprecatedOption : Nat := {
  defValue := 100
  descr    := "my Deprecated option"
}

attribute [deprecated  "This option is deprecated" (since := "2022-07-24")] myDeprecatedOption
