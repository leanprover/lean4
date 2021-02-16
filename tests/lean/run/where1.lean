partial def f (x : Nat) : Nat → Nat
  | 0   => x + 1
  | i+1 => h i + 2
where
  g y := f x y
  h y := g y + 1

def reverse (as : List α) : List α :=
  loop as []
where
  loop : List α → List α → List α
    | [],    acc => acc
    | a::as, acc => loop as (a::acc)

theorem ex : reverse [1, 2, 3] = [3, 2, 1] :=
  rfl

theorem lengthReverse (as : List α) : (reverse as).length = as.length :=
  revLoop as []
where
  revLoop (as bs : List α) : (reverse.loop as bs).length = as.length + bs.length := by
    induction as generalizing bs with
    | nil => simp [reverse.loop]
    | cons a as ih =>
      show (reverse.loop as (a::bs)).length = (a :: as).length + bs.length
      simp [ih, Nat.add_succ, Nat.succ_add]

def h : Nat -> Nat
  | 0    => g 0
  | x+1 => g (h x)
where
  g x := x + 1
