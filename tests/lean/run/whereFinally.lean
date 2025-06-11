example (i j : Nat) (xs : Array Nat) (hi : i < xs.size) (hj: j < xs.size) :=
  match i with
  | 0 => x
  | _ => xs[i]'?_ + xs[j]'?_
where x := 13
finally all_goals assumption

def hole_in_def_body (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  xs[i]'?hole
where finally
  case hole => exact h

def hole_in_def_match (i : Nat) (xs : Array Nat) (h : i < xs.size) : Bool → Nat
  | true => xs[i]'?hole
  | false => i
where finally
  case hole => exact h

def hole_in_def_let_rhs (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let f (_ : Nat) := xs[i]'?hole
  f i
where finally
  case hole => exact h

def hole_in_rec_def_body (n : Nat) (xs : Array Nat) (h : n < xs.size) : Nat :=
  match n with
  | 0 => xs[0]'?hole
  | n + 1 => hole_in_rec_def_body n xs (by omega)
where finally
  case hole => exact h

def hole_in_rec_let_rhs (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    if x = 0 then xs[i]'?hole else f (x-1)
  f i
  where finally
    case hole => exact h

theorem hole_in_thm_body (i : Nat) (xs : Array Nat) (h : i < xs.size) : True :=
  let _x := xs[i]'?hole
  True.intro
where finally
  case hole => exact h

set_option pp.rawOnError true in
def hole_in_def_match_where (i : Nat) (xs : Array Nat) (h : i < xs.size) :=
  match i with
  | 0 => x
  | _ => xs[i]'?hole
where x := 13
finally case hole => assumption

def hole_in_rec_let_rhs_match (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    match x with
    | 0 => xs[i]'?hole
    | x + 1 => x
  f i
  where finally case hole => exact h

def hole_in_rec_let_and_def (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    match x with
    | 0 => xs[i]'?hole
    | x + 1 => x
  f i + xs[i]'?hole₂
where finally
  case hole => exact h
  case hole₂ => exact h

namespace hole_in_mutual_def
mutual
  def even : Nat → Bool
    | 0 => ?zeroEven
    | n + 1 => odd n
  where finally
    case zeroEven => exact true
  def odd : Nat → Bool
    | 0 => ?zeroOdd
    | n + 1 => even n
  where finally
    case zeroOdd => exact false
end

mutual
  def even' (n : Nat) : Bool :=
    let rec go : Nat → Bool
      | 0 => ?zeroEven
      | n + 1 => not (go n)
    go n
  where finally
    case zeroEven => exact true
  def odd' n := not (even' n)
end
end hole_in_mutual_def

structure S where
  a : Nat
  b : Nat

def hole_in_struct_def : S where
  a := ?hole
  b := ?hole₂
where finally
  all_goals exact 42

/--
error: `where ... finally` does not currently support any named sub-sections `| sectionName => ...`
-/
#guard_msgs in
def hole_decreasing_does_not_exist (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  xs[i]'?hole
where finally
  case hole => exact h
| decreasing => skip
