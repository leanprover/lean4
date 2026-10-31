inductive NatTy where
  | nat

inductive NatExt : (Γ : List NatTy) → NatTy → Type where
  | const : Nat → NatExt Γ .nat

def foo  : NatExt Γ B → NatExt Δ B
    | .const a => .const a

/--
error: Failed to realize constant foo.match_1.eq_1:
  failed to generate equality theorems for `match` expression `foo.match_1`
  Γ✝ : List NatTy
  B✝ : NatTy
  motive✝ : NatExt Γ✝ B✝ → Sort u_1
  a✝ : Nat
  h_1✝ : (a : Nat) → motive✝ (NatExt.const a)
  ⊢ (⋯ ▸ fun x motive h_1 h => ⋯ ▸ h_1 a✝) (NatExt.const a✝) motive✝ h_1✝ ⋯ = h_1✝ a✝
---
error: Failed to realize constant foo.match_1.eq_1:
  failed to generate equality theorems for `match` expression `foo.match_1`
  Γ✝ : List NatTy
  B✝ : NatTy
  motive✝ : NatExt Γ✝ B✝ → Sort u_1
  a✝ : Nat
  h_1✝ : (a : Nat) → motive✝ (NatExt.const a)
  ⊢ (⋯ ▸ fun x motive h_1 h => ⋯ ▸ h_1 a✝) (NatExt.const a✝) motive✝ h_1✝ ⋯ = h_1✝ a✝
---
error: Unknown identifier `foo.match_1.eq_1`
-/
#guard_msgs (error, drop info) in
#check foo.match_1.eq_1
