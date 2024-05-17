import Lake.Load.Main

open Lake

-- when `MonadStore1` had an outParam, it was not possible for the following two instances to synthesize

#synth MonadStore1 `key Int $ CycleT Name
  (StateT (NameMap Nat) (StateT (NameMap Int) IO))

#synth MonadStore1 `key Nat $ CycleT Name
  (StateT (NameMap Nat) (StateT (NameMap Int) IO))
