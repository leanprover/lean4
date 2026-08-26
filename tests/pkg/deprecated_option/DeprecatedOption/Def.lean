import Lean

-- Deprecated option without custom text
register_option test.notDeprecated : Bool := {
  defValue := true
  descr := "A non-deprecated test option."
}

@[deprecated test.notDeprecated (since := "2026-04-01")]
register_option test.deprecated.plain : Bool := {
  defValue := false
  descr := "A test option."
}

-- Deprecated option with custom text
@[deprecated "use `test.newOption` instead" (since := "2026-06-01")]
register_option test.deprecated.withText : Nat := {
  defValue := 42
  descr := "Another test option."
}
