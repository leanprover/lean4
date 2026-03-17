inductive InContext : Nat → List Nat → Type
  | here {x : Nat} {xs : List Nat} : InContext x (x::xs)
  | there {x y : Nat} {xs : List Nat} : InContext x xs → InContext x (y::xs)
deriving Ord

inductive Foo : Nat → Nat → Type
  | left {n : Nat} : Foo 0 n
  | right {n : Nat} : Foo n 0
deriving Ord
