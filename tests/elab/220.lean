def f : List Nat → List Nat
  | a::xs@(b::bs) => xs
  | _             => []

#print f
