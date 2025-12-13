inductive N where | z | s (n : N)

-- set_option backwards.match.divide false
-- set_option trace.Meta.Match.match true
-- set_option trace.Meta.Match.matchEqs true

def anyTwo : N → N → N → N → Bool
  | .s .z, _, _ , _ => true
  | _, .s .z, _ , _ => true
  | _, _, .s .z, _ => true
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
      ((x x_4 x_5 : N) → motive x N.z.s x_4 x_5) →
        ((x x_4 x_5 : N) → motive x x_4 N.z.s x_5) →
          ((x x_4 x_5 : N) → motive x x_4 x_5 N.z.s) →
            ((x x_4 x_5 x_6 : N) → motive x x_4 x_5 x_6) → motive x x_1 x_2 x_3 :=
fun motive x x_1 x_2 x_3 h_1 h_2 h_3 h_4 h_5 =>
  have cont_1 := fun x_4 =>
    have cont_2 := fun x_5 =>
      have cont_3 := fun x_6 =>
        anyTwo._sparseCasesOn_1 x_3 (fun n => anyTwo._sparseCasesOn_2 n (h_4 x x_1 x_2) fun h => h_5 x x_1 x_2 n.s)
          fun h => h_5 x x_1 x_2 x_3;
      N.casesOn (motive := fun x_6 => (Unit → motive x x_1 x_6 x_3) → motive x x_1 x_6 x_3) x_2
        (fun cont_3 => cont_3 ())
        (fun n cont_3 =>
          N.casesOn (motive := fun x_6 => (Unit → motive x x_1 x_6.s x_3) → motive x x_1 x_6.s x_3) n
            (fun cont_3 => h_3 x x_1 x_3) (fun n cont_3 => cont_3 ()) cont_3)
        cont_3;
    N.casesOn (motive := fun x_5 => (Unit → motive x x_5 x_2 x_3) → motive x x_5 x_2 x_3) x_1 (fun cont_2 => cont_2 ())
      (fun n cont_2 =>
        N.casesOn (motive := fun x_5 => (Unit → motive x x_5.s x_2 x_3) → motive x x_5.s x_2 x_3) n
          (fun cont_2 => h_2 x x_2 x_3) (fun n cont_2 => cont_2 ()) cont_2)
      cont_2;
  N.casesOn (motive := fun x => (Unit → motive x x_1 x_2 x_3) → motive x x_1 x_2 x_3) x (fun cont_1 => cont_1 ())
    (fun n cont_1 =>
      N.casesOn (motive := fun x => (Unit → motive x.s x_1 x_2 x_3) → motive x.s x_1 x_2 x_3) n
        (fun cont_1 => h_1 x_1 x_2 x_3) (fun n cont_1 => cont_1 ()) cont_1)
    cont_1
-/
#guard_msgs in
#print anyTwo.match_1


/--
info: private def anyTwo.match_1.splitter.{u_1} : (motive : N → N → N → N → Sort u_1) →
  (x x_1 x_2 x_3 : N) →
    ((x x_4 x_5 : N) → motive N.z.s x x_4 x_5) →
      ((x x_4 x_5 : N) → (x = N.z.s → False) → motive x N.z.s x_4 x_5) →
        ((x x_4 x_5 : N) → (x = N.z.s → False) → (x_4 = N.z.s → False) → motive x x_4 N.z.s x_5) →
          ((x x_4 x_5 : N) →
              (x = N.z.s → False) → (x_4 = N.z.s → False) → (x_5 = N.z.s → False) → motive x x_4 x_5 N.z.s) →
            ((x x_4 x_5 x_6 : N) →
                (x = N.z.s → False) →
                  (x_4 = N.z.s → False) → (x_5 = N.z.s → False) → (x_6 = N.z.s → False) → motive x x_4 x_5 x_6) →
              motive x x_1 x_2 x_3
-/
#guard_msgs(pass trace, all) in
#print sig anyTwo.match_1.splitter

inductive Vec (α : Type u) : Nat → Type u
  | zero : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

-- set_option backwards.match.divide false
-- set_option trace.Meta.Match.match true
-- set_option trace.Meta.Match.debug true
-- set_option trace.Meta.Match.matchEqs true

def g (n : Nat) (v w : Vec α n) : Nat :=
  match v, w with
  | .zero, _  => 1
  | _, .cons _ (.cons _ _ ) => 2
  | _, _ => 3

/--
info: private def g.match_1.splitter.{u_1, u_2} : {α : Type u_1} →
  (motive : (n : Nat) → Vec α n → Vec α n → Sort u_2) →
    (n : Nat) →
      (v w : Vec α n) →
        ((x : Vec α 0) → motive 0 Vec.zero x) →
          ((n : Nat) →
              (x : Vec α (n + 1 + 1)) →
                (a a_1 : α) → (a_2 : Vec α n) → motive (n + 1 + 1) x (Vec.cons a (Vec.cons a_1 a_2))) →
            ((n : Nat) →
                (x x_1 : Vec α n) →
                  (∀ (x_2 : Vec α 0), n = 0 → x ≍ Vec.zero → x_1 ≍ x_2 → False) →
                    (∀ (n_1 : Nat) (x_3 : Vec α (n_1 + 1 + 1)) (a a_1 : α) (a_2 : Vec α n_1),
                        n = n_1 + 1 + 1 → x ≍ x_3 → x_1 ≍ Vec.cons a (Vec.cons a_1 a_2) → False) →
                      motive n x x_1) →
              motive n v w
-/
#guard_msgs(pass trace, all) in
#print sig g.match_1.splitter
