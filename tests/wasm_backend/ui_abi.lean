module

public meta import UiAbi

/-!
Tests the stable binary constants shared by the Lean UI and JavaScript host.
-/

open UiAbi

#eval IO.println s!"{magic} {version} {headerSize} {recordSize} {Handler.exact 7}"
