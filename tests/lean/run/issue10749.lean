-- set_option trace.Meta.Match.debug true
-- set_option trace.Meta.Match.match true

set_option match.ignoreUnusedAlts true in
def test (a : List Nat) : Nat :=
  match a with
  | _ => 3
  | [] => 4

-- Should have no `casesOn`

/--
info: def test.match_1.{u_1} : (motive : List Nat → Sort u_1) →
  (a : List Nat) → ((x : List Nat) → motive x) → (Unit → motive []) → motive a :=
fun motive a h_1 h_2 => h_1 a
-/
#guard_msgs in #print test.match_1

def test2 (a b : List Nat) : Nat :=
  match a, b with
  | [], _ => 3
  | _, [] => 4
  | _ :: _, _ :: _ => 5

/--
info: def test2.match_1.{u_1} : (motive : List Nat → List Nat → Sort u_1) →
  (a b : List Nat) →
    ((x : List Nat) → motive [] x) →
      ((x : List Nat) → motive x []) →
        ((head : Nat) →
            (tail : List Nat) → (head_1 : Nat) → (tail_1 : List Nat) → motive (head :: tail) (head_1 :: tail_1)) →
          motive a b :=
fun motive a b h_1 h_2 h_3 =>
  List.casesOn a (h_1 b) fun head tail =>
    List.casesOn b (h_2 (head :: tail)) fun head_1 tail_1 => h_3 head tail head_1 tail_1
-/
#guard_msgs in #print test2.match_1

def test3 (a : List Nat) (b : Bool) : Nat :=
  match a, b with
  | _, true => 0
  | [], _ => 1
  | _, _ => 2

-- Should have exactly two `casesOn`

/--
info: def test3.match_1.{u_1} : (motive : List Nat → Bool → Sort u_1) →
  (a : List Nat) →
    (b : Bool) →
      ((x : List Nat) → motive x true) →
        ((x : Bool) → motive [] x) → ((x : List Nat) → (x_1 : Bool) → motive x x_1) → motive a b :=
fun motive a b h_1 h_2 h_3 =>
  Bool.casesOn b (List.casesOn a (h_2 false) fun head tail => h_3 (head :: tail) false) (h_1 a)
-/
#guard_msgs in #print test3.match_1

set_option maxHeartbeats 100 in
example (P : Nat → Prop) (x : Nat) (h : x = 12345) (hP : P 12345) : P x :=
  match x, h with | _, rfl => hP


def test4 : Bool → Bool → Bool → Bool → Bool → Bool
  | _, _ , _ , _ , true => true
  | _, _ , _ , true , _ => true
  | _, _ , true , _ , _ => true
  | _, true , _ , _ , _ => true
  | true , _ , _ , _ , _ => true
  | _ , _ , _ , _ , _ => false

/--
info: def test4.match_1.{u_1} : (motive : Bool → Bool → Bool → Bool → Bool → Sort u_1) →
  (x x_1 x_2 x_3 x_4 : Bool) →
    ((x x_5 x_6 x_7 : Bool) → motive x x_5 x_6 x_7 true) →
      ((x x_5 x_6 x_7 : Bool) → motive x x_5 x_6 true x_7) →
        ((x x_5 x_6 x_7 : Bool) → motive x x_5 true x_6 x_7) →
          ((x x_5 x_6 x_7 : Bool) → motive x true x_5 x_6 x_7) →
            ((x x_5 x_6 x_7 : Bool) → motive true x x_5 x_6 x_7) →
              ((x x_5 x_6 x_7 x_8 : Bool) → motive x x_5 x_6 x_7 x_8) → motive x x_1 x_2 x_3 x_4 :=
fun motive x x_1 x_2 x_3 x_4 h_1 h_2 h_3 h_4 h_5 h_6 =>
  Bool.casesOn x_4
    (Bool.casesOn x_3
      (Bool.casesOn x_2
        (Bool.casesOn x_1 (Bool.casesOn x (h_6 false false false false false) (h_5 false false false false))
          (h_4 x false false false))
        (h_3 x x_1 false false))
      (h_2 x x_1 x_2 false))
    (h_1 x x_1 x_2 x_3)
-/
#guard_msgs in
#print test4.match_1
