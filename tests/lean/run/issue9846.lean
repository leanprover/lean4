def testMatch : Array α → Unit
  | #[_] => ()
  | _ => ()

/--
error: Failed to realize constant testMatch.match_1.eq_1:
  failed to generate equality theorems for `match` expression `testMatch.match_1`
  case isTrue
  α✝ : Type u_1
  motive✝ : Array α✝ → Sort u_2
  x✝¹ : Array α✝
  h_1✝ : (head : α✝) → motive✝ #[head]
  h_2✝ : (x : Array α✝) → motive✝ x
  x✝ : ∀ (head : α✝), x✝¹ = #[head] → False
  h✝ : x✝¹.size = 1
  ⊢ (⋯ ▸ fun h => ⋯ ▸ h_1✝ (x✝¹.getLit 0 ⋯ ⋯)) ⋯ = h_2✝ x✝¹
---
error: Unknown constant `testMatch.match_1.eq_1`
-/
#guard_msgs in
#print testMatch.match_1.eq_1
