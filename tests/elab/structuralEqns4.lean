inductive N where | zero | succ (n : N)

/--
info: protected theorem N.brecOn.eq.{u} : ∀ {motive : N → Sort u} (t : N) (F_1 : (t : N) → N.below t → motive t),
  N.brecOn t F_1 = F_1 t (N.brecOn.go t F_1).2
-/
#guard_msgs in #print sig N.brecOn.eq

-- set_option trace.Elab.definition.structural.eqns true

def g (i : Nat) (j : N) : N :=
  if i < 5 then .zero else
  match j with
  | .zero => N.zero.succ
  | .succ j => g i j
termination_by structural j


/--
info: theorem g.eq_def : ∀ (i : Nat) (j : N),
  g i j =
    if i < 5 then N.zero
    else
      match j with
      | N.zero => N.zero.succ
      | j.succ => g i j
-/
#guard_msgs(pass trace, all) in #print sig g.eq_def


def N.beq : (m n : N) → Bool
| .zero, .zero => true
| .succ m, .succ n => N.beq m n
| _, _ => false

/--
info: theorem N.beq.eq_def : ∀ (x x_1 : N),
  x.beq x_1 =
    match x, x_1 with
    | N.zero, N.zero => true
    | m.succ, n.succ => m.beq n
    | x, x_2 => false
-/
#guard_msgs(pass trace, all) in #print sig N.beq.eq_def
