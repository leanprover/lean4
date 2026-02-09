def f1 (xs : Option (Array Nat)) : Nat :=
  match xs with
  | some #[x, y] => x
  | _ => 0


def f2 (xs : Option (Array Nat)) : Nat :=
  match xs with
  | some #[0, y]   => y
  | some #[x+1, y] => x
  | _              => 0

theorem ex1 : f2 (some #[0, 2]) = 2  := rfl
theorem ex2 : f2 (some #[10, 2]) = 9 := rfl

def f3 (xs : Option (Array (Array Nat))) : Nat :=
  match xs with
  | some #[#[0], #[x]]    => x
  | some #[#[x+1], #[y]]  => x
  | _                     => 0

theorem ex3 : f3 (some #[#[10], #[5]]) = 9 := rfl
theorem ex4 : f3 (some #[#[0], #[5]])  = 5 := rfl
theorem ex5 : f3 (some #[#[0], #[5], #[4]]) = 0 := rfl

#check match some #[1, 2] with
  | some #[x, y] => x
  | _ => 0
