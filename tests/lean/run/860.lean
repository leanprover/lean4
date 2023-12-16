def evenq (n: Nat) : Bool := Nat.mod n 2 = 0

private theorem pack_loop_terminates : (n : Nat) → n / 2 < n.succ
  | 0   => by decide
  | 1   => by decide
  | n+2 => by
    rw [Nat.div_eq]
    split
    · rw [Nat.add_sub_self_right]
      have := pack_loop_terminates n
      calc n/2 + 1 < Nat.succ n + 1   := Nat.add_le_add_right this 1
           _       < Nat.succ (n + 2) := Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.lt_succ_self _))
    · apply Nat.zero_lt_succ

def pack (n: Nat) : List Nat :=
  let rec loop (n : Nat) (acc : Nat) (accs: List Nat) : List Nat :=
    let next (n: Nat) := n / 2;
    match n with
    | Nat.zero => List.cons acc accs
    | n+1 => match evenq n with
      | true => loop (next n) 0 (List.cons acc accs)
      | false => loop (next n) (acc+1) accs
  loop n 0 []
termination_by _ n _ _ => n
decreasing_by
  simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel]
  apply pack_loop_terminates

#eval pack 27
