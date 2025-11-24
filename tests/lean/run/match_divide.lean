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

example : anyTwo N.z.s .z .z .z = true := by rfl
example : anyTwo .z .z .z N.z.s = true := by rfl
example : anyTwo N.z.s.s .z .z N.z.s = true := by rfl
example : anyTwo .z .z .z N.z.s = true := by rfl

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → N → N → Sort u_1) →
  (x x_1 x_2 x_3 : N) →
    ((x x_4 x_5 : N) → motive N.z.s x x_4 x_5) →
      ((x x_4 x_5 : N) → motive x x_4 x_5 N.z.s) →
        ((x x_4 x_5 x_6 : N) → motive x x_4 x_5 x_6) → motive x x_1 x_2 x_3 :=
fun motive x x_1 x_2 x_3 h_1 h_2 h_3 =>
  have cont_1 := fun x_4 =>
    anyTwo._sparseCasesOn_1 (motive := fun x_5 =>
      (∀ (x_6 x_7 x_8 : N), x_8 = x_5 → x_7 = x_2 → x_6 = x_1 → N.z.s = x → False) → motive x x_1 x_2 x_5) x_3
      (fun n x_5 =>
        anyTwo._sparseCasesOn_2 (motive := fun x_6 =>
          (∀ (x_7 x_8 x_9 : N), x_9 = x_6.s → x_8 = x_2 → x_7 = x_1 → N.z.s = x → False) → motive x x_1 x_2 x_6.s) n
          (fun x_6 => h_2 x x_1 x_2) (fun h x_6 => h_3 x x_1 x_2 n.s) x_5)
      (fun h x_5 => h_3 x x_1 x_2 x_3) x_4;
  N.casesOn (motive := fun x =>
    ((∀ (x_4 x_5 x_6 : N), x_6 = x_3 → x_5 = x_2 → x_4 = x_1 → N.z.s = x → False) → motive x x_1 x_2 x_3) →
      motive x x_1 x_2 x_3)
    x (fun cont_1 => cont_1 ⋯)
    (fun n cont_1 =>
      N.casesOn (motive := fun x =>
        ((∀ (x_4 x_5 x_6 : N), x_6 = x_3 → x_5 = x_2 → x_4 = x_1 → N.z.s = x.s → False) → motive x.s x_1 x_2 x_3) →
          motive x.s x_1 x_2 x_3)
        n (fun cont_1 => h_1 x_1 x_2 x_3) (fun n cont_1 => cont_1 ⋯) cont_1)
    cont_1
-/
#guard_msgs in
#print anyTwo.match_1


/--
error: Failed to realize constant anyTwo.match_1.splitter:
  failed to generate equality theorem `_private.lean.run.match_divide.0.anyTwo.match_1.eq_2` for `match` expression `anyTwo.match_1`
  case s.z
  motive✝ : N → N → N → N → Sort u_1
  x✝¹ x✝ : N
  h_1✝ : (x x_1 x_2 : N) → motive✝ N.z.s x x_1 x_2
  h_2✝ : (x x_1 x_2 : N) → motive✝ x x_1 x_2 N.z.s
  h_3✝ : (x x_1 x_2 x_3 : N) → motive✝ x x_1 x_2 x_3
  ⊢ h_1✝ x✝¹ x✝ N.z.s = h_2✝ N.z.s x✝¹ x✝
---
error: Unknown constant `anyTwo.match_1.splitter`
-/
#guard_msgs(pass trace, all) in
#print sig anyTwo.match_1.splitter
