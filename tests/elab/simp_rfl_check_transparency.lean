set_option simp.rfl.checkTransparency true

-- `myId` is at default transparency, not reducible.
def myId (n : Nat) : Nat := n

-- LHS `myId n` and RHS `n` are only defeq if `myId` is unfolded.
-- `[backward_defeq]` accepts this; `[simp]` triggers `simp.rfl.checkTransparency`,
-- which warns since the lemma is now considered `rfl` (via `[backward_defeq]`+useBackward
-- or via `[defeq]`).
@[simp] theorem myId_eq (n : Nat) : myId n = n := (rfl)

-- `implicit_reducible` version is fine for `[defeq]`.
@[implicit_reducible] def myId2 (n : Nat) : Nat := n

#guard_msgs in
@[defeq, simp] theorem myId2_eq (n : Nat) : myId2 n = n := rfl
