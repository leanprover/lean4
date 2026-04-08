/-!
# Make sure there is type information on `_` for inst parameters in explicit mode
-/

example : Nat := @ite _ True _ 1 2
                           --^ textDocument/hover
