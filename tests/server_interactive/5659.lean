/-!
  # `rintro` and `intro` error message should point to excess arg

  Below, the errors should point to `h` because there is no lambda it binds.
  The error should not point to `hn`; it would be OKish to underline the whole line. -/

example : (∃ n : Nat, n < 0) → False := by
  rintro ⟨n, hn⟩ h
              --^ collectDiagnostics

example : (∃ n : Nat, n < 0) → False := by
  intro ⟨n, hn⟩ h
             --^ collectDiagnostics
