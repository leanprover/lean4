/-!
Info nodes for syntax that is elaborated beside a tactic hole must not be discarded.

`elabTypeAscription` elaborates `Nat` and then returns the metavariable of the `by` block, so the
term info for `Nat` used to be dropped together with the trees of the surrounding node.
-/

example : Nat := (by exact 0 : Nat)
                              --^ textDocument/hover

example : Nat := ((by exact 0 : Nat))
                               --^ textDocument/hover

example : Nat := (0 : Nat)
                     --^ textDocument/hover
