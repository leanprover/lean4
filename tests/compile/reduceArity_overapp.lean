def tuple (types : List Type) : Type :=
  match types with
  | [] => Unit
  | [t] => t
  | t :: types => t × tuple types

def uncurried ins out := tuple ins -> out

def curried (ins : List Type) out := match ins with
  | [] => out
  | (x :: xs) => x -> curried xs out

def curry (f : uncurried ins out) : curried ins out :=
  match ins with
  | [] => f ()
  | [_] => f
  | (_ :: _ :: _) => λx => curry (λxs => f (x, xs))

def main : IO Unit := do
  let val : String := curry (ins := [Int, String]) Prod.snd 1 "a"
  IO.println val
