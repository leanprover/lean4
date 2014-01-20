variable matrix : Nat → Nat → Type
variable mul {m n p : Nat} : matrix n m → matrix m p → matrix n p
infixl 70 * : mul
axiom mul_assoc {m n p o : Nat} (M : matrix n m) (N : matrix m p) (P : matrix p o) :
      M * (N * P) = (M * N) * P
add_rewrite mul_assoc

-- Create an example
variable m1 : matrix 2 3
variable m2 : matrix 3 4
variable m3 : matrix 4 2
variable m4 : matrix 2 6

(*
local t = parse_lean("m1 * (m2 * (m3 * m4))")
print("before simp: " .. tostring(t))
print("after simp:  " .. tostring(simplify(t)))
*)