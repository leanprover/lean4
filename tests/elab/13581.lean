-- https://github.com/leanprover/lean4/issues/13581
-- Reporting `diagnostics` must not crash on private match/sparseCasesOn helpers
-- in module mode under a `public section`.
module

public section

def onlyTrue : Bool → Bool
  | true => true
  | x    => x

#guard_msgs (drop trace) in
set_option diagnostics true in
set_option diagnostics.threshold 0 in
example : onlyTrue true = true := rfl
