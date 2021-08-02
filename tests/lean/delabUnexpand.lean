structure Foo where
  x : Nat
  y : Nat

macro a:term " ♬ " b:term : term => `(Foo.mk $a $b)

@[appUnexpander Foo.mk] def unexpandFooFailure1 : Lean.PrettyPrinter.Unexpander
  | _ => throw ()

@[appUnexpander Foo.mk] def unexpandFoo : Lean.PrettyPrinter.Unexpander
  | `(Foo.mk $a $b) => `($a ♬ $b)
  | _ => throw ()

@[appUnexpander Foo.mk] def unexpandFooFailure2 : Lean.PrettyPrinter.Unexpander
  | _ => throw ()

#check 3 ♬ 4

def foo (k : Nat → Nat) (n : Nat) : Nat := k (n+1)

@[appUnexpander foo] def unexpandFooApp : Lean.PrettyPrinter.Unexpander
  | `(foo $k $a) => `(My.foo $k $a)
  | _ => throw ()

#check foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ foo $ id
