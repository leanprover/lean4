inductive NatTy where
  | nat

inductive NatExt : (Γ : List NatTy) → NatTy → Type where
  | const : Nat → NatExt Γ .nat

def foo  : NatExt Γ B → NatExt Δ B
    | .const a => .const a

#guard_msgs (error, drop info) in
#check foo.match_1.eq_1
