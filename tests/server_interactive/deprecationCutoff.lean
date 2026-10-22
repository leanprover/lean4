module

/-! Editing a deprecation cutoff must refresh warnings in subsequent commands. -/

set_option linter.deprecated true
set_option deprecation.warnings.local "2000-01-01"
--⬑ collectDiagnostics
                                     --^ change: "2000-01-01" "2000-01-02"
--⬑ collectDiagnostics
                                     --^ change: "2000-01-02" "2000-01-01"
--⬑ collectDiagnostics

@[deprecated "old local name" (since := "2000-01-02")]
def oldName : Nat := 1

example : Nat := oldName
