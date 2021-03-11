@[noinline] def f (x : Bool)   := x
@[noinline] def g (x y : Bool) := x

def h (x : Bool) (xs : List Nat) : List Bool :=
  match x with
  | true =>
    let z := f true
    let y := f false
    xs.map fun x => g y z
  | false =>
    let y := f false
    let z := f true
    xs.map fun x => g y z

theorem ex1 : h true [1] = h false [1] := rfl

#eval h true [1]
#eval h false [1]

theorem ex2 : (h true [1] == h false [1]) = true :=
  by nativeDecide

@[noinline] def f2 (a : String) := a
@[noinline] def g2 (a : String) (x : Bool) := a

def h2 (x : Bool) (xs : List Nat) : List String :=
  match x with
  | false =>
    let a := f2 "a"
    let y := f false
    xs.map fun x => g2 a y
  | true =>
    let y := f false
    let a := f2 "a"
    xs.map fun x => g2 a y

#eval h2 true [1]
#eval h2 false [1]
