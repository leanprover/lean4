structure State -- TODO

structure Expr -- TODO

def eval : State → Expr → Bool :=
  fun _ _ => true

inductive Command where
  | skip
  | cond  : Expr → Command → Command → Command
  | while : Expr → Command → Command
  | seq   : Command → Command → Command

open Command

infix:10 ";;" => Command.seq

inductive Bigstep : Command × State → State → Nat → Prop where
  | skip    : Bigstep (skip, σ) σ 1
  | seq     : Bigstep (c₁, σ₁) σ₂ t₁ → Bigstep (c₂, σ₂) σ₃ t₂ → Bigstep (c₁ ;; c₂, σ₁) σ₃ (t₁ + t₂ + 1)
  | ifTrue  : eval σ₁ b = true  → Bigstep (c₁, σ₁) σ₂ t → Bigstep (cond b c₁ c₂, σ₁) σ₂ (t + 1)
  | ifFalse : eval σ₁ b = false → Bigstep (c₂, σ₁) σ₂ t → Bigstep (cond b c₁ c₂, σ₁) σ₂ (t + 1)

#check @Bigstep.seq

namespace WithoutAutoImplicit

set_option autoBoundImplicitLocal false

inductive Bigstep : Command × State → State → Nat → Prop where
  | skip    {σ} : Bigstep (skip, σ) σ 1
  | seq     {c₁ c₂ σ₁ σ₂ σ₃ t₁ t₂} : Bigstep (c₁, σ₁) σ₂ t₁ → Bigstep (c₂, σ₂) σ₃ t₂ → Bigstep (c₁ ;; c₂, σ₁) σ₃ (t₁ + t₂ + 1)
  | ifTrue  {b c₁ c₂ σ₁ σ₂ t} : eval σ₁ b = true  → Bigstep (c₁, σ₁) σ₂ t → Bigstep (cond b c₁ c₂, σ₁) σ₂ (t + 1)
  | ifFalse {b c₁ c₂ σ₁ σ₂ t} : eval σ₁ b = false → Bigstep (c₂, σ₁) σ₂ t → Bigstep (cond b c₁ c₂, σ₁) σ₂ (t + 1)

end WithoutAutoImplicit
