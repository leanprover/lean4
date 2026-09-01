instance {m} {σ} [Pure m] : Pure (StateT σ m) :=
  let rec pure {α} (a s) := Pure.pure (a, s)
  { pure := @pure }

instance {m} {σ} [Pure m] : Pure (StateT σ m) :=
  let rec pure {α} (a : α) (s : σ) := Pure.pure (a, s)
  { pure := pure }

instance {m} {σ} [Pure m] : Pure (StateT σ m) :=
  let rec pure {α} (a : α) := fun s => Pure.pure (a, s)
  { pure := pure }

instance {m} {σ} [Pure m] : Pure (StateT σ m) :=
  let rec pure {α} (a : α) : StateT σ m α := fun s => Pure.pure (a, s)
  { pure := pure }
