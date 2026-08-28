inductive N : Type where | z : N | s : N → N

/-- info: N.ctorIdx : N → Nat -/
#guard_msgs in
#check N.ctorIdx

/-- info: N.ctorIdx.hinj (x x' : N) (x_eq : x = x') : x.ctorIdx = x'.ctorIdx -/
#guard_msgs in
#check N.ctorIdx.hinj

inductive Vec (α : Type) : Nat → Type where
| nil  : Vec α 0
| cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)

/--
info: Vec.ctorIdx.hinj {α : Type} {a✝ : Nat} (x : Vec α a✝) {α' : Type} {a'✝ : Nat} (x' : Vec α' a'✝) (α_eq : α = α') :
  a✝ = a'✝ → ∀ (x_eq : x ≍ x'), x.ctorIdx = x'.ctorIdx
-/
#guard_msgs in
#check Vec.ctorIdx.hinj


inductive EvenVec (α : Type) : (n : Nat) → (n % 2 = 0) → Type where
| nil  : EvenVec α 0 (by rfl)
| cons : α → EvenVec α n p → EvenVec α (n + 2) (by grind)

-- NB: No HEq between the proof arguments (they are not needed)

/--
info: EvenVec.ctorIdx.hinj {α : Type} {n : Nat} {a✝ : n % 2 = 0} (x : EvenVec α n a✝) {α' : Type} {n' : Nat}
  {a'✝ : n' % 2 = 0} (x' : EvenVec α' n' a'✝) (α_eq : α = α') (n_eq : n = n') (x_eq : x ≍ x') : x.ctorIdx = x'.ctorIdx
-/
#guard_msgs in
#check EvenVec.ctorIdx.hinj
