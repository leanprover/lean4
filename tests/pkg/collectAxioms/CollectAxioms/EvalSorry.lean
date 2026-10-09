module

public meta import CollectAxioms.SorryCodeVia

/-! `#eval` detects `sorry` in the compiled code of imported declarations. -/

/--
error: Aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs in
#eval sorryInCode false

/-! This also holds for code reached through further modules. -/

/--
error: Aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs in
#eval viaSorryCode false
