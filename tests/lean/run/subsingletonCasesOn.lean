def addAndMatch (a₁ a₂ : Array Nat) (i j : Nat) (and : And (i < a₁.size) (j < a₂.size)) : Nat :=
  match and with
  | ⟨p, q⟩ => a₁[i] + a₂[j]

def addAndCasesOn (a₁ a₂ : Array Nat) (i j : Nat) (and : And (i < a₁.size) (j < a₂.size)) : Nat :=
  and.casesOn fun p q => a₁[i] + a₂[j]

/-- info: 9 -/
#guard_msgs in
#eval addAndMatch #[1, 2, 3] #[4, 5, 6, 7] 1 3 (And.intro (by grind) (by grind))

/-- info: 9 -/
#guard_msgs in
#eval addAndCasesOn #[1, 2, 3] #[4, 5, 6, 7] 1 3 (And.intro (by grind) (by grind))

structure Und (P Q : Prop) : Prop where
  p : P
  q : Q

def addUndMatch (a₁ a₂ : Array Nat) (i j : Nat) (and : Und (i < a₁.size) (j < a₂.size)) : Nat :=
  match and with
  | ⟨p, q⟩ => a₁[i] + a₂[j]

def addUndCasesOn (a₁ a₂ : Array Nat) (i j : Nat) (and : Und (i < a₁.size) (j < a₂.size)) : Nat :=
  and.casesOn fun p q => a₁[i] + a₂[j]

/-- info: 8 -/
#guard_msgs in
#eval addUndMatch #[1, 2, 3] #[4, 5, 6, 7] 2 1 (Und.mk (by grind) (by grind))

/-- info: 8 -/
#guard_msgs in
#eval addUndCasesOn #[1, 2, 3] #[4, 5, 6, 7] 2 1 (Und.mk (by grind) (by grind))

def castEqMatch (n₁ n₂ : Nat) (eq : Eq n₁ n₂) (v : Vector Nat n₁) : Vector Nat n₂ :=
  match eq with
  | .refl _ => v

def castEqCasesOn (n₁ n₂ : Nat) (eq : Eq n₁ n₂) (v : Vector Nat n₁) : Vector Nat n₂ :=
  eq.casesOn v

/-- info: 5 -/
#guard_msgs in
#eval castEqMatch (1 + 3) (2 + 2) (.refl 4) #[2, 3, 5, 7].toVector |>.get 2

/-- info: 5 -/
#guard_msgs in
#eval castEqCasesOn (1 + 3) (2 + 2) (.refl 4) #[2, 3, 5, 7].toVector |>.get 2

inductive Eek {α : Type} : α → α → Prop where
  | refl (a : α) : Eek a a

def castEekMatch (n₁ n₂ : Nat) (eq : Eek n₁ n₂) (v : Vector Nat n₁) : Vector Nat n₁ :=
  match eq with
  | .refl _ => v

def castEekCasesOn (n₁ n₂ : Nat) (eq : Eek n₁ n₂) (v : Vector Nat n₁) : Vector Nat n₁ :=
  eq.casesOn v

/-- info: 7 -/
#guard_msgs in
#eval castEekMatch (1 + 3) (2 + 2) (.refl 4) #[2, 3, 5, 7].toVector |>.get 3

/-- info: 7 -/
#guard_msgs in
#eval castEekCasesOn (1 + 3) (2 + 2) (.refl 4) #[2, 3, 5, 7].toVector |>.get 3
