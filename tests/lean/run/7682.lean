/-- Test that monad instances and operations for `Except ε` and `ExceptT ε Id`
are definitionally equal. -/

example ε : ExceptT.instMonad (ε:=ε) (m:=Id) = Except.instMonad (ε:=ε) := rfl
example ε α : @ExceptT.pure ε Id _ α = @Except.pure ε α := rfl
example ε α β : @ExceptT.map ε Id _ α β = @Except.map ε α β := rfl
example ε α β : @ExceptT.adapt ε Id _ α β = @Except.mapError ε α β := rfl
example ε α β : @ExceptT.bind ε Id _ α β = @Except.bind ε α β := rfl
example ε α β : @ExceptT.tryCatch ε Id _ α β = @Except.tryCatch ε α β := rfl
example ε : instMonadExceptOfExceptTOfMonad (ε:=ε) (m:=Id) = Except.instMonadExceptOf (ε:=ε) := rfl
