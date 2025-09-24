@[simp] def range : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: range n

attribute [simp] List.range
