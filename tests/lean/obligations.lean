def obligation_in_def_body (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  xs[i]'?hole
obligations_by
  case hole => exact h

def obligation_in_def_match (i : Nat) (xs : Array Nat) (h : i < xs.size) : Bool → Nat
  | true => xs[i]'?hole
  | false => i
obligations_by
  case hole => exact h

def obligation_in_def_let_rhs (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let f (_ : Nat) := xs[i]'?hole
  f i
obligations_by
  case hole => exact h

def obligation_in_rec_def_body (n : Nat) (xs : Array Nat) (h : n < xs.size) : Nat :=
  match n with
  | 0 => xs[0]'?hole
  | n + 1 => obligation_in_rec_def_body n xs (by omega)
obligations_by
  case hole => exact h

def obligation_in_rec_let_rhs (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    if x = 0 then xs[i]'?hole else f (x-1)
  obligations_by
    case hole => exact h
  f i

theorem obligation_in_thm_body (i : Nat) (xs : Array Nat) (h : i < xs.size) : True :=
  let _x := xs[i]'?hole
  True.intro
obligations_by
  case hole => exact h

def obligation_in_def_match_where (i : Nat) (xs : Array Nat) (h : i < xs.size) :=
  match i with
  | 0 => 0
  | _ => xs[i]'?hole
  where x := 13;
obligations_by
  case hole => assumption

def obligation_in_rec_let_rhs_match (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    match x with
    | 0 => xs[i]'?hole
    | x + 1 => x
  obligations_by
    case hole => exact h
  f i

def obligation_in_rec_let_and_def (i : Nat) (xs : Array Nat) (h : i < xs.size) : Nat :=
  let rec f (x : Nat) :=
    match x with
    | 0 => xs[i]'?hole
    | x + 1 => x
  obligations_by
    case hole => exact h
  f i + xs[i]'?hole₂
obligations_by
  case hole₂ => exact h
