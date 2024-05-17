import Lake.Load.Main

open Lake

-- when `MonadStore1` had an outParam, one of the following instances could not be synthesized, as an outParam can only be one value

#synth MonadStore1 `key Int $ CycleT Name
  (StateT (NameMap Nat) (StateT (NameMap Int) IO))

#synth MonadStore1 `key Nat $ CycleT Name
  (StateT (NameMap Nat) (StateT (NameMap Int) IO))
