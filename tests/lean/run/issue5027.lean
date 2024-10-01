inductive Term (α: Type): Type where
  | Composite : Array (Term α) → Term α
  | Atom: α → Term α

-- height of a term
def height (f: Term α): Nat :=
  let rec max_height (a: Array (Term α)) (i: Nat) (m: Nat): Nat :=
    if h: i < a.size then
      -- The recursive call to height used to fail because of a too weak
      -- array_get_dec
      max_height a (i + 1) (max (height a[i]) m)
    else
      m
  match f with
  | .Composite a => 1 + max_height a 0 0
  | .Atom _ => 1
