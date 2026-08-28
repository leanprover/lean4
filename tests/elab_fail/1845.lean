import Lean.Hygiene
import Lean.Exception
open Lean

def bar : StateT Nat Unhygienic Syntax.Term := do modify (· + 1); `("hi")
def foo : StateT Nat Unhygienic Syntax.Term := do `(throwError $(← bar))

#eval Unhygienic.run (foo.run 0) |>.2

-- don't do this
syntax "←" term : term

def foo' : StateT Nat Unhygienic Syntax.Term := do `(throwError $(← bar))
