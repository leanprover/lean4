def Mine := Id

class MyMonad (m) extends Monad m where
  bind_eq_bind : @bind = @bind := by trivial

instance : MyMonad Mine where
  -- should show me all the fields I need to fill in
  -- excluding default and auto-param fields
  -- i.e., only `pure` and `bind`
