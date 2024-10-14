import SimplcLean._root_

-- TODO: move this to the library??
@[simp] theorem Functor.map_pure [Monad m] [LawfulMonad m] {a : α} : (f <$> pure a : m β) = pure (f a) := by
  simp [pure, map]

-- I can't work out why this isn't closed by `Functor.map_map`.
simp_lc whitelist LawfulMonad.bind_pure_comp bind_map_left

#guard_msgs (drop info) in
simp_lc check in Monad LawfulMonad _root_ ExceptT
