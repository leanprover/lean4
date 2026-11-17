inductive NatTy where
  | nat

inductive NatExt : (Γ : List NatTy) → NatTy → Type where
  | const : Nat → NatExt Γ .nat

def foo  : NatExt Γ B → NatExt Δ B
    | .const a => .const a

/--
error: Failed to realize constant foo.match_1.eq_1:
  Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
    x✝ ≍ NatExt.const a✝
  
  Γ✝ : List NatTy
  B✝ : NatTy
  motive✝ : NatExt Γ✝ B✝ → Sort u_1
  x✝ : NatExt Γ✝ B✝
  h_1✝ : (a : Nat) → motive✝ (NatExt.const a)
  a✝ : Nat
  heq_1✝ : x✝ ≍ NatExt.const a✝
  ⊢ (match x✝ with
      | NatExt.const a => h_1✝ a) ≍
      h_1✝ a✝
---
error: Failed to realize constant foo.match_1.eq_1:
  Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
    x✝ ≍ NatExt.const a✝
  
  Γ✝ : List NatTy
  B✝ : NatTy
  motive✝ : NatExt Γ✝ B✝ → Sort u_1
  x✝ : NatExt Γ✝ B✝
  h_1✝ : (a : Nat) → motive✝ (NatExt.const a)
  a✝ : Nat
  heq_1✝ : x✝ ≍ NatExt.const a✝
  ⊢ (match x✝ with
      | NatExt.const a => h_1✝ a) ≍
      h_1✝ a✝
---
error: Unknown identifier `foo.match_1.eq_1`
-/
#guard_msgs (error, drop info) in
#check foo.match_1.eq_1
