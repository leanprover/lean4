abbrev DelabM := Id
abbrev Delab := DelabM Nat

example : DelabM Nat := pure 1  -- works
-- example : Delab := pure 1    -- fails in old frontend

new_frontend

example : DelabM Nat := pure 1  -- works
example : Delab := pure 1       -- works
