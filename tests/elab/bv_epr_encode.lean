import Lean
import Std.Tactic.BVDecide

/-!
Tests for the `BitVec` encoding of many-sorted EPR problems, `epr2BitVec`. Every encoded fact is type
checked against its proof.
-/

open Lean Meta Elab Tactic Tactic.BVDecide
open Std.Tactic.BVDecide.EPR.BitVec

elab "epr_encode" : tactic => do
  let g ← getMainGoal
  g.withContext <| Sym.SymM.run do
    let mut hyps : Array Normalize.Hyp := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless ← isProp decl.type do continue
      hyps := hyps.push {
        name := decl.userName
        type := ← Sym.shareCommon (← instantiateMVars decl.type)
        value := decl.toExpr
        source := .lctx decl.fvarId
      }
    let res ← EPR.detectEprProblem hyps
    let bvProblem ← EPR.epr2BitVec res.problem g
    for fact in bvProblem.groundFacts ++ bvProblem.quantifiedFacts.map (·.hyp) do
      check fact.value
      unless ← isDefEq (← inferType fact.value) fact.type do
        throwError m!"Proof of encoded fact{indentExpr fact.type}\nhas type{indentExpr (← inferType fact.value)}"
      logInfo m!"{fact.type}"

-- Ground facts, including equalities between elements.
/--
info: ¬toBvPred₁ [a, b] a P (toBvAux [a, b] ⋯ a) = 1#1
---
info: ¬toBvAux [a, b] ⋯ a = toBvAux [a, b] ⋯ b
---
info: toBvAux [a, b] ⋯ a < 2#2
---
info: toBvAux [a, b] ⋯ b < 2#2
-/
#guard_msgs (info, drop warning) in
example (α : Type) (a b : α) (P : α → Prop) (h1 : ¬P a) (h2 : a ≠ b) : False := by
  epr_encode
  sorry

-- Facts do not need to be in NNF.
/--
info: ¬(toBvPred₁ [a, b] a P (toBvAux [a, b] ⋯ a) = 1#1 ∧
    (toBvPred₂ [a, b] a [a, b] a Q (toBvAux [a, b] ⋯ a) (toBvAux [a, b] ⋯ b) = 1#1 ↔
      toBvAux [a, b] ⋯ a = toBvAux [a, b] ⋯ b))
---
info: toBvPred₁ [a, b] a P (toBvAux [a, b] ⋯ b) = 1#1 →
  ¬toBvPred₂ [a, b] a [a, b] a Q (toBvAux [a, b] ⋯ b) (toBvAux [a, b] ⋯ a) = 1#1
---
info: toBvAux [a, b] ⋯ a < 2#2
---
info: toBvAux [a, b] ⋯ b < 2#2
-/
#guard_msgs (info, drop warning) in
example (α : Type) (a b : α) (P : α → Prop) (Q : α → α → Prop) (h1 : ¬(P a ∧ (Q a b ↔ a = b)))
    (h2 : P b → ¬Q b a) : False := by
  epr_encode
  sorry

-- Quantified facts over multiple sorts.
/--
info: toBvAux [b₁, b₂] ⋯ b₁ < 2#2
---
info: toBvAux [b₁, b₂] ⋯ b₂ < 2#2
---
info: toBvAux [a] ⋯ a < 1#1
---
info: ∀ (x : α) (y : β),
  toBvAux [a] ⋯ x = toBvAux [a] ⋯ a →
    toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₁ ∨ toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₂ →
      toBvPred₂ [a] a [b₁, b₂] b₁ R (toBvAux [a] ⋯ x) (toBvAux [b₁, b₂] ⋯ y) = 1#1 →
        toBvPred₁ [b₁, b₂] b₁ Q (toBvAux [b₁, b₂] ⋯ y) = 1#1 ∨ toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₁
---
info: ∀ (y : β),
  toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₁ ∨ toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₂ →
    ¬(toBvPred₁ [b₁, b₂] b₁ Q (toBvAux [b₁, b₂] ⋯ y) = 1#1 ↔ toBvAux [b₁, b₂] ⋯ y = toBvAux [b₁, b₂] ⋯ b₂)
-/
#guard_msgs (info, drop warning) in
example (α β : Type) (a : α) (b₁ b₂ : β) (R : α → β → Prop) (Q : β → Prop)
    (h1 : ∀ x y, R x y → Q y ∨ y = b₁) (h2 : ∀ y, ¬(Q y ↔ y = b₂)) : False := by
  epr_encode
  sorry

-- Elements obtained from a `Nonempty` instance.
/--
info: toBvAux [Classical.ofNonempty] ⋯ Classical.ofNonempty < 1#1
---
info: ∀ (x : α),
  toBvAux [Classical.ofNonempty] ⋯ x = toBvAux [Classical.ofNonempty] ⋯ Classical.ofNonempty →
    toBvPred₁ [Classical.ofNonempty] Classical.ofNonempty P (toBvAux [Classical.ofNonempty] ⋯ x) = 1#1
---
info: ∀ (x : α),
  toBvAux [Classical.ofNonempty] ⋯ x = toBvAux [Classical.ofNonempty] ⋯ Classical.ofNonempty →
    ¬toBvPred₁ [Classical.ofNonempty] Classical.ofNonempty P (toBvAux [Classical.ofNonempty] ⋯ x) = 1#1
-/
#guard_msgs (info, drop warning) in
example (α : Type) [Nonempty α] (P : α → Prop) (h1 : ∀ x, P x) (h2 : ∀ x, ¬P x) : False := by
  epr_encode
  sorry

-- Propositional atoms are left untouched.
/--
info: toBvAux [a] ⋯ a < 1#1
---
info: ∀ (x : α), toBvAux [a] ⋯ x = toBvAux [a] ⋯ a → toBvPred₁ [a] a P (toBvAux [a] ⋯ x) = 1#1 → q
-/
#guard_msgs (info, drop warning) in
example (α : Type) (a : α) (P : α → Prop) (q : Prop) (h1 : ∀ x, P x → q) : False := by
  epr_encode
  sorry


-- Equalities between propositions.
/--
info: (toBvPred₁ [a] a P (toBvAux [a] ⋯ a) = 1#1) = False
---
info: toBvAux [a] ⋯ a < 1#1
---
info: ∀ (x : α),
  toBvAux [a] ⋯ x = toBvAux [a] ⋯ a →
    (toBvPred₁ [a] a P (toBvAux [a] ⋯ x) = 1#1) = (toBvPred₁ [a] a Q (toBvAux [a] ⋯ x) = 1#1)
-/
#guard_msgs (info, drop warning) in
example (α : Type) (a : α) (P Q : α → Prop) (h1 : ∀ x, P x = Q x) (h2 : P a = False) : False := by
  epr_encode
  sorry
