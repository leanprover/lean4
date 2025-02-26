inductive Foo : Nat → Type where
| foo: (Nat → Foo n) → Foo n

-- structural recursion failed, produced type incorrect term

/--
error: fail to show termination for
  Foo.bar
with errors
failed to infer structural recursion:
Not considering parameter #2 of Foo.bar:
  its type is an inductive datatype
    Foo x✝¹
  and the datatype parameter
    x✝¹
  depends on the function parameter
    x✝¹
  which is not fixed.
Cannot use parameter #1:
  failed to eliminate recursive application
    (f 0).bar


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            n #1
1) 36:14-23 =  ?

#1: sizeOf x2

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
def Foo.bar : {n: Nat} → Foo n → Foo n
| _, foo f => (f 0).bar

-- it works
def Foo.bar' {n: Nat} : Foo n → Foo n
| foo f => (f 0).bar'
