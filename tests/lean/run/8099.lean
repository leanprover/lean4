
example : List Bool :=
  let s : String := "test"
  let l : List Nat := [1, 2, 3]
  let r := match 1 with | _ => l.map (fun n => let (x) := s; true)
  []

example : List Bool :=
  let p : String × String := ("test", "test")
  let l : List Nat := [1, 2, 3]
  let o : Option Nat := none
  let r :=
    match o with
    | none => [false]
    | some m => l.map (fun n => let (x, y) := p; true)
  []

-- Previously, the `contradiction` below would fail because the `match` would have been generalized.
-- That was because the expected type of the `match` was a metavariable that was not properly
-- abstracted over `a`; hence the `matchType` was type incorrect and generalization failed to
-- re-introduce `ha : 42 = 37`.
example (a : Nat) (ha : a = 37) :=
  (match a with | 42 => by contradiction | n => n) = 37

example (n : Nat) : Id (Fin (n + 1)) :=
  have jp : ?m := ?rhs
  match n with
  | 0 => ?jmp1
  | n + 1 => ?jmp2
  where finally
  case m => exact Fin (n + 1) → Id (Fin (n + 1))
  case jmp1 => exact jp ⟨0, by decide⟩
  case jmp2 => exact jp ⟨n, by omega⟩
  case rhs => exact pure
