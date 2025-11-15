inductive N where | z | s (n : N)

-- set_option backwards.match.divide false

-- set_option trace.Meta.Match.match true
set_option trace.Meta.Match.matchEqs true

def anyTwo : N → N → N → N → Bool
  | .s .z, _, _ , _ => true
  -- | _, .s .z, _ , _ => true
  -- | _, _, .s .z, _ => true
  | _, _, _, .s .z => true
  | _, _, _, _ => false

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → N → N → Sort u_1) →
  (x x_1 x_2 x_3 : N) →
    ((x x_4 x_5 : N) → motive N.z.s x x_4 x_5) →
      ((x x_4 x_5 : N) → motive x x_4 x_5 N.z.s) →
        ((x x_4 x_5 x_6 : N) → motive x x_4 x_5 x_6) → motive x x_1 x_2 x_3 :=
fun motive x x_1 x_2 x_3 h_1 h_2 h_3 =>
  have cont_1 :=
    anyTwo._sparseCasesOn_1 x_3 (fun n => anyTwo._sparseCasesOn_2 n (h_2 x x_1 x_2) fun h_0 => h_3 x x_1 x_2 n.s)
      fun h_0 => h_3 x x_1 x_2 x_3;
  anyTwo._sparseCasesOn_1 (motive := fun x => motive x x_1 x_2 x_3 → motive x x_1 x_2 x_3) x
    (fun n cont_1 =>
      anyTwo._sparseCasesOn_2 (motive := fun x => motive x.s x_1 x_2 x_3 → motive x.s x_1 x_2 x_3) n
        (fun cont_1 => h_1 x_1 x_2 x_3) (fun h_0 cont_1 => cont_1) cont_1)
    (fun h_0 cont_1 => cont_1) cont_1
-/
#guard_msgs in
#print anyTwo.match_1


/--
error: Failed to realize constant anyTwo.match_1.splitter:
  failed to generate splitter for match auxiliary declaration `anyTwo.match_1`, unsolved subgoal:
  case x
  motive : N → N → N → N → Sort u_1
  x✝² x✝¹ x✝ : N
  h_1 : (x x_1 x_2 : N) → motive N.z.s x x_1 x_2
  h_2 : (x x_1 x_2 : N) → (x = N.z.s → False) → motive x x_1 x_2 N.z.s
  h_3 : (x x_1 x_2 x_3 : N) → (x = N.z.s → False) → (x_3 = N.z.s → False) → motive x x_1 x_2 x_3
  n✝ : N
  ⊢ False
---
error: Failed to realize constant anyTwo.match_1.splitter:
  failed to generate splitter for match auxiliary declaration `anyTwo.match_1`, unsolved subgoal:
  case x
  motive : N → N → N → N → Sort u_1
  x✝² x✝¹ x✝ : N
  h_1 : (x x_1 x_2 : N) → motive N.z.s x x_1 x_2
  h_2 : (x x_1 x_2 : N) → (x = N.z.s → False) → motive x x_1 x_2 N.z.s
  h_3 : (x x_1 x_2 x_3 : N) → (x = N.z.s → False) → (x_3 = N.z.s → False) → motive x x_1 x_2 x_3
  n✝ : N
  ⊢ False
---
error: Unknown identifier `anyTwo.match_1.splitter`
-/
#guard_msgs(pass trace, all) in
#check anyTwo.match_1.splitter
