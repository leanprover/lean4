set_option linter.unusedVariables false
set_option genSizeOfSpec false

inductive W₁ where
  | c : List ({w : Nat} → W₁) → W₁


inductive W₂ where
  | a : List ((y : Nat) → W₂) → W₂
  | c : List ({w : Nat} → W₂) → W₂


/-- info: W₁.c : List ({w : Nat} → W₁) → W₁ -/
#guard_msgs in
#check @W₁.c

/-- info: W₂.a : List (Nat → W₂) → W₂ -/
#guard_msgs in
#check @W₂.a

/-- info: W₂.c : List ({w : Nat} → W₂) → W₂ -/
#guard_msgs in
#check @W₂.c
