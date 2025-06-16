/-! Equational theorem generation regression test.-/

structure PrefixTable (α : Type _) extends Array (α × Nat) where
  /-- Validity condition to help with termination proofs -/
  valid : (h : i < toArray.size) → toArray[i].2 ≤ i

def PrefixTable.step [BEq α] (t : PrefixTable α) (x : α) (kf : Fin (t.size+1)) : Fin (t.size+1) :=
  match kf with
  | ⟨k, hk⟩ =>
    let cont := fun () =>
      match k with
      | 0 => ⟨0, Nat.zero_lt_succ _⟩
      | k + 1 =>
        have h2 : k < t.size := Nat.lt_of_succ_lt_succ hk
        let k' := t.toArray[k].2
        have hk' : k' < k + 1 := Nat.lt_succ_of_le (t.valid h2)
        step t x ⟨k', Nat.lt_trans hk' hk⟩
    if hsz : k < t.size then
      if x == t.toArray[k].1 then
        ⟨k+1, Nat.succ_lt_succ hsz⟩
      else cont ()
    else cont ()
termination_by kf.val

/--
info: PrefixTable.step.eq_def.{u_1} {α : Type u_1} [BEq α] (t : PrefixTable α) (x : α) (kf : Fin (t.size + 1)) :
  t.step x kf =
    match kf with
    | ⟨k, hk⟩ =>
      let cont := fun x_1 =>
        match k, hk with
        | 0, hk => ⟨0, ⋯⟩
        | k.succ, hk =>
          let_fun h2 := ⋯;
          let k' := t.toArray[k].snd;
          let_fun hk' := ⋯;
          t.step x ⟨k', ⋯⟩;
      if hsz : k < t.size then if (x == t.toArray[k].fst) = true then ⟨k + 1, ⋯⟩ else cont () else cont ()
-/
#guard_msgs in
#check PrefixTable.step.eq_def
