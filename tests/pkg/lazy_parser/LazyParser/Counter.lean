/-!
Counts evaluations of the parser `countedTerm` from `LazyParser.Def`. It lives in its own module so
that its initializer has run when `LazyParser.Def` evaluates the parser.
-/

initialize forceCount : IO.Ref Nat ← IO.mkRef 0
