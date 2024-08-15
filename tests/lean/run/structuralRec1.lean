set_option linter.unusedVariables false

inductive PList (α : Type) : Prop
| nil
| cons : α → PList α → PList α

infixr:67 " ::: " => PList.cons

def map {α β} (f : α → β) : List α → List β
| []    => []
| a::as => f a :: map f as

def pmap {α β} (f : α → β) : PList α → PList β
| PList.nil => PList.nil
| a:::as => f a ::: pmap f as

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

def pmap2 {α β} (f : α → β) (as : PList α) : PList β :=
let rec loop : PList α → PList β
 | PList.nil    => PList.nil
 | a:::as => f a ::: loop as;
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

def pfoo (xs : PList Nat) : PList Nat :=
match xs with
| PList.nil   => PList.nil
| x:::xs =>
  let y := 2 * x;
  match xs with
  | PList.nil    => PList.nil
  | x:::xs => (y + x) ::: pfoo xs

#guard foo [1, 2, 3, 4] == [4, 10]

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

def pbla (x : Nat) (ys : PList Nat) : PList Nat :=
if x % 2 == 0 then
  match ys with
  | PList.nil    => PList.nil
  | y:::ys => (y + x/2) ::: pbla (x/2) ys
else
  match ys with
  | PList.nil    => PList.nil
  | y:::ys => (y + x/2 + 1) ::: pbla (x/2) ys
termination_by structural ys

theorem blaEq (y : Nat) (ys : List Nat) : bla 4 (y::ys) = (y+2) :: bla 2 ys :=
rfl

inductive PNat : Prop
| zero
| succ : PNat → PNat

def f : Nat → Nat → Nat
 | 0, y   => y
 | x+1, y =>
   match f x y with
   | 0 => f x y
   | v => f x v + 1

def pf : PNat → PNat → PNat
 | PNat.zero, y   => y
 | PNat.succ x, y =>
   match pf x y with
   | PNat.zero => pf x y
   | v => PNat.succ $ pf x v

def g (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | y::ys =>
    match ys with
    | [] => 1
    | _ => g ys + 1

def pg (xs : PList Nat) : True :=
  match xs with
  | PList.nil => True.intro
  | y:::ys =>
    match ys with
    | PList.nil => True.intro
    | _ => pg ys

def aux : Nat → Nat → Nat
 | 0, y   => y
 | x+1, y =>
   match f x y with
   | 0 => f x y
   | v => f x v + 1

def paux : PNat → PNat → PNat
 | PNat.zero, y   => y
 | PNat.succ x, y =>
   match pf x y with
   | PNat.zero => pf x y
   | v => PNat.succ (pf x v)

theorem ex (x y : Nat) : f x y = aux x y := by
  cases x
  rfl
  rfl

axiom F : Nat → Nat

inductive is_nat : Nat -> Prop
| Z : is_nat 0
| S {n} : is_nat n → is_nat (F n)

inductive is_nat_T : Nat -> Type
| Z : is_nat_T 0
| S {n} : is_nat_T n → is_nat_T (F n)

axiom P : Nat → Prop
axiom F0 : P 0
axiom F1 : P (F 0)
axiom FS {n : Nat} : P n → P (F (F n))

axiom T : Nat → Prop
axiom TF0 : T 0
axiom TF1 : T (F 0)
axiom TFS {n : Nat} : T n → T (F (F n))

-- set_option trace.Elab.definition.structural true in
theorem «nested recursion» : ∀ {n}, is_nat n → P n
| _, is_nat.Z => F0
| _, is_nat.S is_nat.Z => F1
| _, is_nat.S (is_nat.S h) => FS («nested recursion» h)

/-- forbidding this, because it shouldn't exist in the first place.
    We don't expect this kind of inconsistent inaccessible patterns. -/
-- theorem «nested recursion, inaccessible» : ∀ {n}, is_nat n → P n
-- | _, .(is_nat.Z) => F0
-- | _, is_nat.S .(is_nat.Z) => F1
-- | _, is_nat.S (is_nat.S h) => FS («nested recursion, inaccessible» h)

theorem «reordered discriminants, type» : ∀ n, is_nat_T n → Nat → T n := fun n hn m =>
match n, m, hn with
| _, _, is_nat_T.Z => TF0
| _, _, is_nat_T.S is_nat_T.Z => TF1
| _, m, is_nat_T.S (is_nat_T.S h) => TFS («reordered discriminants, type» _ h m)


theorem «reordered discriminants» : ∀ n, is_nat n → Nat → P n := fun n hn m =>
match n, m, hn with
| _, _, is_nat.Z => F0
| _, _, is_nat.S is_nat.Z => F1
| _, m, is_nat.S (is_nat.S h) => FS («reordered discriminants» _ h m)
termination_by structural _ n => n

/-- known unsupported case for types, just here for reference. -/
-- def «unsupported nesting» (xs : List Nat) : True :=
--   match xs with
--   | List.nil => True.intro
--   | y::ys =>
--     match ys with
--     | List.nil      => True.intro
--     | _::_::zs      => «unsupported nesting» zs
--     | zs            => «unsupported nesting» ys

def «unsupported nesting, predicate» (xs : PList Nat) : True :=
  match xs with
  | PList.nil => True.intro
  | y:::ys =>
    match ys with
    | PList.nil      => True.intro
    | _:::_:::zs     => «unsupported nesting, predicate» zs
    | zs             => «unsupported nesting, predicate» ys


def f1 (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs =>
  match xs with
  | []  => 0
  | _ => f1 xs + 1

def pf1 (xs : PList Nat) : True :=
match xs with
| PList.nil => True.intro
| x:::xs =>
  match xs with
  | PList.nil  => True.intro
  | _ => pf1 xs
