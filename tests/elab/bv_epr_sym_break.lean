import Lean
import Std.Tactic.BVDecide

/-!
Tests for the `eprSymBreak` option of `bv_decide +epr`: the facts each mode adds to the encoding, that
all modes prove the same theorems, and that `simple` and `full` restrict which encodings models use.
-/

open Std.Tactic.BVDecide.EPR.BitVec

-- Every mode bounds the encoding to the elements, `simple` and `full` add ordering constraints.
/--
trace: α : Type
a b c : α
h1✝ : ¬a = c
h2✝ : ¬b = c
h1 : (!toBvAux [a, b, c] ⋯ a == toBvAux [a, b, c] ⋯ c) = true
h2 : (!toBvAux [a, b, c] ⋯ b == toBvAux [a, b, c] ⋯ c) = true
a✝² : (!toBvAux [a, b, c] ⋯ a == 3#2) = true
a✝¹ : (!toBvAux [a, b, c] ⋯ b == 3#2) = true
a✝ : (!toBvAux [a, b, c] ⋯ c == 3#2) = true
⊢ False
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a b c : α) (h1 : a ≠ c) (h2 : b ≠ c) : False := by
  bv_normalize +epr (eprSymBreak := .off)
  trace_state
  sorry

/--
trace: α : Type
a b c : α
h1✝ : ¬a = c
h2✝ : ¬b = c
h1 : (!toBvAux [a, b, c] ⋯ a == toBvAux [a, b, c] ⋯ c) = true
h2 : (!toBvAux [a, b, c] ⋯ b == toBvAux [a, b, c] ⋯ c) = true
a✝² : (toBvAux [a, b, c] ⋯ a == 0#2) = true
a✝¹ : (!(1#2).ult (toBvAux [a, b, c] ⋯ b)) = true
a✝ : (!(2#2).ult (toBvAux [a, b, c] ⋯ c)) = true
⊢ False
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a b c : α) (h1 : a ≠ c) (h2 : b ≠ c) : False := by
  bv_normalize +epr (eprSymBreak := .simple)
  trace_state
  sorry

/--
trace: α : Type
a b c : α
h1✝ : ¬a = c
h2✝ : ¬b = c
h1 : (!toBvAux [a, b, c] ⋯ a == toBvAux [a, b, c] ⋯ c) = true
h2 : (!toBvAux [a, b, c] ⋯ b == toBvAux [a, b, c] ⋯ c) = true
a✝³ : (toBvAux [a, b, c] ⋯ a == 0#2) = true
a✝² : (!(1#2).ult (toBvAux [a, b, c] ⋯ b)) = true
a✝¹ : (!(toBvAux [a, b, c] ⋯ b == 0#2 && toBvAux [a, b, c] ⋯ c == 1#2)) = true
a✝ : (!(2#2).ult (toBvAux [a, b, c] ⋯ c)) = true
⊢ False
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a b c : α) (h1 : a ≠ c) (h2 : b ≠ c) : False := by
  bv_normalize +epr (eprSymBreak := .full)
  trace_state
  sorry

section Unsat

variable (α : Type) (a b c : α) (R : α → α → Prop)

example (h1 : a = c) (h2 : ∀ x y, R x y → R y x) (h3 : R a b) (h4 : ¬R b c) : False := by
  bv_decide +epr +uf (eprSymBreak := .off)

example (h1 : a = c) (h2 : ∀ x y, R x y → R y x) (h3 : R a b) (h4 : ¬R b c) : False := by
  bv_decide +epr +uf (eprSymBreak := .simple)

example (h1 : a = c) (h2 : ∀ x y, R x y → R y x) (h3 : R a b) (h4 : ¬R b c) : False := by
  bv_decide +epr +uf (eprSymBreak := .full)

end Unsat

section Sat

-- Distinct elements are forced to their own position.
/--
error: The prover found a counterexample, consider the following assignment:
a = α₀
b = α₁
c = α₂
-/
#guard_msgs in
example (α : Type) (a b c : α) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : False := by
  bv_decide +epr +uf (eprSymBreak := .simple)

end Sat

section Facts

open Lean Meta Elab Term in
/-- The encoding of `x` in width `w`, with the proof term `epr2BitVec` uses so the atoms coincide. -/
elab "encoded" w:num elems:term:max x:term:max : term => do
  let elems ← elabTerm elems none
  let x ← elabTerm x none
  let α ← inferType x
  let .sort (.succ u) ← inferType α | throwError "expected a type"
  let w := w.getNat
  let lt ← mkDecideProof (← mkLt (← mkAppM ``List.length #[elems]) (toExpr (2 ^ w)))
  return mkApp5 (mkConst ``toBvAux [u]) α (toExpr w) elems lt x

/-!
Hypotheses about the encoding itself show which facts each mode makes available to the solver:
`simple` refutes `b = 2`, `full` additionally refutes `b = 0 ∧ c = 1`.
-/

variable (α : Type) (a b c : α)

/--
error: The prover found a counterexample, consider the following assignment:
b = α₂
a = α₁
c = α₁
-/
#guard_msgs in
example (h1 : a = c) (h2 : b ≠ c) (h3 : encoded 2 [a, b, c] b = 2#2) : False := by
  bv_decide +epr +uf (eprSymBreak := .off)

example (h1 : a = c) (h2 : b ≠ c) (h3 : encoded 2 [a, b, c] b = 2#2) : False := by
  bv_decide +epr +uf (eprSymBreak := .simple)

/--
error: The prover found a counterexample, consider the following assignment:
c = α₁
a = α₀
b = α₀
-/
#guard_msgs in
example (h1 : a = b) (h2 : c ≠ a) (h3 : encoded 2 [a, b, c] c = 1#2) : False := by
  bv_decide +epr +uf (eprSymBreak := .simple)

example (h1 : a = b) (h2 : c ≠ a) (h3 : encoded 2 [a, b, c] c = 1#2) : False := by
  bv_decide +epr +uf (eprSymBreak := .full)

end Facts
