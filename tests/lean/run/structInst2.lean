import Init.Control.Option

new_frontend

def optMonad {m} [Monad m] : Monad (OptionT m) :=
{ pure := OptionT.pure, bind := OptionT.bind }

def optAlt {m} [Monad m] : Alternative (OptionT m) :=
{ failure       := OptionT.fail,
  orelse        := OptionT.orelse,
  toApplicative := Monad.toApplicative (OptionT m) } -- TODO: check toApplicative binder annotations
