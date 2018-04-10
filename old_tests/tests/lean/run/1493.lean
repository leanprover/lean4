open tactic.interactive

meta def bug : tactic unit := do
_ ← solve1 refl,
return ()
