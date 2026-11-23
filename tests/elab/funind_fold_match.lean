/-!
Functional induction: recursive calls inside a `match` that refines the induction hypothesis must
be folded back to calls of the function when that `match` ends up in the induction principle,
e.g. in the condition of an `if`.
-/

def h (n : Nat) : Nat := if (match n with | n+1 => h n | _ => 0) = 0 then 1 else 2
termination_by structural n

/--
info: h.induct (motive : Nat → Prop)
  (case1 :
    ∀ (t : Nat),
      (match t with
          | n.succ => h n
          | x => 0) =
          0 →
        (match t with
          | n.succ => motive n
          | x => True) →
          motive t)
  (case2 :
    ∀ (t : Nat),
      ¬(match t with
            | n.succ => h n
            | x => 0) =
            0 →
        (match t with
          | n.succ => motive n
          | x => True) →
          motive t)
  (n : Nat) : motive n
-/
#guard_msgs in
#check h.induct

def hLet (n : Nat) : Nat :=
  let x := match n with | n+1 => hLet n | _ => 0
  if x = 0 then 1 else 2
termination_by structural n

/--
info: hLet.induct (motive : Nat → Prop)
  (case1 :
    ∀ (t : Nat),
      have x :=
        match t with
        | n.succ => hLet n
        | x => 0;
      x = 0 →
        (match t with
          | n.succ => motive n
          | x => True) →
          motive t)
  (case2 :
    ∀ (t : Nat),
      have x :=
        match t with
        | n.succ => hLet n
        | x => 0;
      ¬x = 0 →
        (match t with
          | n.succ => motive n
          | x => True) →
          motive t)
  (n : Nat) : motive n
-/
#guard_msgs in
#check hLet.induct

-- Deeply nested matches must not cause exponential work
def hDeep (n : Nat) : Nat := if (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => (match n with | n+1 => hDeep n | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) | _ => 0) = 0 then 1 else 2
termination_by structural n

#guard_msgs (drop info) in
#check hDeep.induct
