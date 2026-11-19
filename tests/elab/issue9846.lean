def testMatch : Array α → Unit
  | #[_] => ()
  | _ => ()

/--
error: Failed to realize constant testMatch.match_1.eq_1:
  failed to generate equality theorems for `match` expression `testMatch.match_1`
  case isTrue
  α✝ : Type u_1
  motive✝ : Array α✝ → Sort u_2
  x✝² : Array α✝
  h_1✝ : (head : α✝) → motive✝ #[head]
  h_2✝ : (x : Array α✝) → motive✝ x
  x✝¹ : Array α✝
  x✝ : ∀ (head : α✝), x✝² = #[head] → False
  h✝ : x✝².size = 1
  ⊢ (⋯ ▸ fun h => ⋯ ▸ h_1✝ (x✝².getLit 0 ⋯ ⋯)) ⋯ = h_2✝ x✝²
---
error: Unknown constant `testMatch.match_1.eq_1`
-/
#guard_msgs in
#print testMatch.match_1.eq_1
