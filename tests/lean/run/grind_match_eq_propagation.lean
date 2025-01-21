inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

def f (x y : S) :=
  match x, y with
  | .mk1 _, _ => 2
  | _, .mk2 1 (.mk4 _ _) => 3
  | .mk3 _, _ => 4
  | _, _ => 5

example : f a b < 2 → b = .mk2 y1 y2 → y1 = 2 → a = .mk4 y3 y4 → False := by
  unfold f
  grind (splits := 0)

example : b = .mk2 y1 y2 → y1 = 2 → a = .mk4 y3 y4 → f a b = 5 := by
  unfold f
  grind (splits := 0)

example : b = .mk2 y1 y2 → y1 = 2 → a = .mk3 n → f a b = 4 := by
  unfold f
  grind (splits := 0)

example : b = .mk2 y1 y2 → y1 = 1 → y2 = .mk4 s1 s2 → a = .mk3 n → f a b = 3 := by
  unfold f
  grind (splits := 0)

example : b = .mk2 y1 y2 → y1 = 1 → y2 = .mk4 s1 s2 → a = .mk2 s3 s4 → f a b = 3 := by
  unfold f
  grind (splits := 0)

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def g (v w : Vec α n) : Nat :=
  match v, w with
  | _, .cons _ (.cons _ _) => 20
  | .nil, _ => 30
  | _, _    => 40

-- TODO: introduce casts while instantiating equation theorems for `g.match_1`
-- example (a b : Vec α 2) : g a b = 20 := by
--  unfold g
--  grind
