/-!
Benchmark for the `arith` simproc of `Sym.simp` on polynomial expansions over `Int`, `Nat`,
commutative rings and semirings, and noncommutative rings.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c d e : Int) : (a + b + c + d + e)^7 = (a + b + c + d + e)^3 * (a + b + c + d + e)^4 := by sym => simp arithSimp

example (a b : Int) : (a + b)^40 = (a + b)^20 * (a + b)^20 := by sym => simp arithSimp

example (a b c : Int) : (a + 2 * b + 3 * c)^12 = ((a + 2 * b + 3 * c)^4)^3 := by sym => simp arithSimp

example (a b c d e : Nat) : (a + b + c + d + e)^7 = (a + b + c + d + e)^3 * (a + b + c + d + e)^4 := by sym => simp arithSimp

example (a b : Nat) : (a + b)^40 = (a + b)^20 * (a + b)^20 := by sym => simp arithSimp

example (a b c : Nat) : (a + 2 * b + 3 * c)^12 = ((a + 2 * b + 3 * c)^4)^3 := by sym => simp arithSimp

example [Lean.Grind.CommRing α] (a b c d e : α) : (a + b + c + d + e)^6 = (a + b + c + d + e)^2 * (a + b + c + d + e)^4 := by sym => simp arithSimp

example [Lean.Grind.CommSemiring α] (a b c d : α) : (a + b + c + d)^6 = (a + b + c + d)^3 * (a + b + c + d)^3 := by sym => simp arithSimp

example [Lean.Grind.Ring α] (a b c : α) : (a + b + c)^2 = a^2 + b^2 + c^2 + a*b + b*a + a*c + c*a + b*c + c*b := by sym => simp arithSimp

example (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Int) :
    (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) =
      (a₁*b₁ - a₂*b₂ - a₃*b₃ - a₄*b₄)^2 + (a₁*b₂ + a₂*b₁ + a₃*b₄ - a₄*b₃)^2 +
      (a₁*b₃ - a₂*b₄ + a₃*b₁ + a₄*b₂)^2 + (a₁*b₄ + a₂*b₃ - a₃*b₂ + a₄*b₁)^2 := by sym => simp arithSimp

example (x y z w : Int) : (x - y)^2 * (y - z)^2 * (z - w)^2 * (w - x)^2 = ((x - y) * (y - z) * (z - w) * (w - x))^2 := by sym => simp arithSimp

example (a b c : Nat) : (a + 1) * (b + 2) * (c + 3) * (a + b + c + 4) * (a * b + c + 5) = (a * b + c + 5) * (a + b + c + 4) * (c + 3) * (b + 2) * (a + 1) := by sym => simp arithSimp

example (a b c : Int) :
    let t := (a + b + c)^2
    let u := t * t - t
    u * u + u * t = t * (u + u * t) - t * u + u * u + u * t - t * u * t := by intros; sym => simp arithSimp
