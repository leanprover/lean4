import Lean

-- Deprecated option without custom text
register_option test.deprecated.plain : Bool := {
  defValue := false
  descr := "A test option."
  deprecation? := some { since := "2026-04-01" }
}

-- Deprecated option with custom text
register_option test.deprecated.withText : Nat := {
  defValue := 42
  descr := "Another test option."
  deprecation? := some { since := "2026-04-01", text? := some "use `test.newOption` instead" }
}

-- Non-deprecated option (for comparison)
register_option test.notDeprecated : Bool := {
  defValue := true
  descr := "A non-deprecated test option."
}
