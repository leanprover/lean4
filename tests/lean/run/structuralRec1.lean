new_frontend

def map {α β} (f : α → β) : List α → List β
| []    => []
| a::as => f a :: map f as

theorem ex1 : map Nat.succ [1] = [2] :=
rfl

theorem ex2 : map Nat.succ [] = [] :=
rfl

theorem ex3 (a : Nat) : map Nat.succ [a] = [Nat.succ a] :=
rfl

theorem ex4 {α β} (f : α → β) (a : α) (as : List α) : map f (a::as) = (f a) :: map f as :=
rfl

theorem ex5 {α β} (f : α → β) : map f [] = [] :=
rfl

def map2 {α β} (f : α → β) (as : List α) : List β :=
let rec loop : List α → List β
 | []    => []
 | a::as => f a :: loop as;
loop as

theorem ex6 {α β} (f : α → β) (a : α) (as : List α) : map2 f (a::as) = (f a) :: map2 f as :=
rfl

def foo (xs : List Nat) : List Nat :=
match xs with
| []    => []
| x::xs =>
  let y := 2 * x;
  match xs with
  | []    => []
  | x::xs => (y + x) :: foo xs

#eval foo [1, 2, 3, 4]

theorem fooEq (x y : Nat) (xs : List Nat) : foo (x::y::xs) = (2*x + y) :: foo xs :=
rfl

def bla (x : Nat) (ys : List Nat) : List Nat :=
if x % 2 == 0 then
  match ys with
  | []    => []
  | y::ys => (y + x/2) :: bla (x/2) ys
else
  match ys with
  | []    => []
  | y::ys => (y + x/2 + 1) :: bla (x/2) ys

theorem blaEq (y : Nat) (ys : List Nat) : bla 4 (y::ys) = (y+2) :: bla 2 ys :=
rfl
