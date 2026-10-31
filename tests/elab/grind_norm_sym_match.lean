/-!
`match` equations under the `Sym.simp`-based `grind` normalizer. E-matching instances of match
equations carry the annotations `Grind.simpMatchDiscrsOnly` (only the discriminants of the
`match` may be simplified) and `Grind.PreMatchCond` (the condition must keep the shape produced
by `annotateMatchEqnType`); the normalizer must respect both.
-/

set_option backward.grind.normalizer false
set_option grind.debug true

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
  grind (splits := 0) [f.eq_def]

example : b = .mk2 y1 y2 → y1 = 2 → a = .mk4 y3 y4 → f a b = 5 := by
  grind (splits := 0) [f.eq_def]

example : b = .mk2 y1 y2 → y1 = 2 → a = .mk3 n → f a b = 4 := by
  grind (splits := 0) [f.eq_def]

example : b = .mk2 y1 y2 → y1 = 1 → y2 = .mk4 s1 s2 → a = .mk3 n → f a b = 3 := by
  grind (splits := 0) [f.eq_def]

example : b = .mk2 y1 y2 → y1 = 1 → y2 = .mk4 s1 s2 → a = .mk2 s3 s4 → f a b = 3 := by
  grind (splits := 0) [f.eq_def]

-- Discriminants are normalized (`x + 0`), the alternatives are not touched
def g (x : Nat) (y : Nat) : Nat :=
  match x + 0 with
  | 0 => y + 0
  | n + 1 => n

example (h : g 3 y = 5) : False := by grind [g.eq_def]
example : g (n + 1) y = n := by grind [g.eq_def]
example : g 0 y = y := by grind [g.eq_def]

example (x n : Nat)
    : 0 < match x with
          | 0  => 1
          | _ => x + n := by
  grind

example (x y : Nat)
    : 0 < match x, y with
          | 0, 0   => 1
          | _, _ => x + y := by
  grind

def h : List Nat → Nat
  | [] => 0
  | x :: xs => x + h xs

example : h (x :: xs) = x + h xs := by grind [h.eq_def]
