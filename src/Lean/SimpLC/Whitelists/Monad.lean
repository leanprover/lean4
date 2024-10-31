import Lean.SimpLC.Whitelists.Root

-- TODO: move this to the library??
@[simp] theorem Functor.map_pure [Monad m] [LawfulMonad m] {a : α} : (f <$> pure a : m β) = pure (f a) := by
  simp [pure, map]

-- I can't work out why this isn't closed by `Functor.map_map`.
simp_lc whitelist LawfulMonad.bind_pure_comp bind_map_left

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Monad LawfulMonad _root_ ExceptT
