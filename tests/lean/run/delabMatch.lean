import Lean
/-!
# Testing the `delabAppMatch` delaborator
-/


/-!
Basic functionality
-/
/--
info: def Nat.pred : Nat → Nat :=
fun x =>
  match x with
  | 0 => 0
  | a.succ => a
-/
#guard_msgs in
#print Nat.pred
/--
info: def List.head?.{u} : {α : Type u} → List α → Option α :=
fun {α} x =>
  match x with
  | [] => none
  | a :: tail => some a
-/
#guard_msgs in
#print List.head?


/-!
`h :` annotations
-/
/--
info: fun x =>
  let_fun this :=
    match h : ↑x + 1 with
    | 0 => Nat.noConfusion h
    | n.succ => Exists.intro n (Nat.succ.inj h);
  this : ∀ (x : Fin 1), ∃ n, ↑x = n
-/
#guard_msgs in
#check fun (x : Fin 1) => show ∃ (n : Nat), x = n from
  match h : x.1 + 1 with
  | 0 => Nat.noConfusion h
  | n + 1 => ⟨n, Nat.succ.inj h⟩


/-!
Shadowing with `h :` annotations
-/
/--
info: fun h =>
  let_fun this :=
    match h_1 : ↑h + 1 with
    | 0 => Nat.noConfusion h_1
    | n.succ => Exists.intro n (Nat.succ.inj h_1);
  this : ∀ (h : Fin 1), ∃ n, ↑h = n
-/
#guard_msgs in
#check fun (h : Fin 1) => show ∃ (n : Nat), h = n from
  match h : h.1 + 1 with
  | 0 => Nat.noConfusion h
  | n + 1 => ⟨n, Nat.succ.inj h⟩


/-!
Even more shadowing with `h :` annotations
-/
set_option linter.unusedVariables false in
/--
info: fun h =>
  let_fun this :=
    match h_1 : ↑h + 1 with
    | 0 => Nat.noConfusion h_1
    | h_2.succ => Exists.intro h_2 (Nat.succ.inj h_1);
  this : ∀ (h : Fin 1), ∃ n, ↑h = n
-/
#guard_msgs in
#check fun (h : Fin 1) => show ∃ (n : Nat), h = n from
  match h : h.1 + 1 with
  | 0 => Nat.noConfusion h
  | h + 1 => ⟨_, Nat.succ.inj ‹_›⟩


/-!
Overapplication
-/
/--
info: fun b =>
  (match (motive := Bool → Bool → Bool) b with
    | false => fun x => x
    | true => fun x => !x)
    b : Bool → Bool
-/
#guard_msgs in
#check (fun b : Bool => (match b with | false => fun x => x | true => fun x => !x) b)


namespace WithFoo

def foo (b : Bool) : Bool := match b with | false => false | _ => b


/-!
Follows the names from the functions
-/
set_option linter.unusedVariables false in
/--
info: fun b =>
  match b with
  | false => false
  | a => b : Bool → Bool
-/
#guard_msgs in
#check fun b => foo.match_1 (fun _ => Bool) b (fun _ => false) fun a => b


/-!
Underapplied, no `match` notation
-/
set_option linter.unusedVariables false in
/-- info: fun b => foo.match_1 (fun x => Bool) b fun x => false : Bool → (Bool → Bool) → Bool -/
#guard_msgs in
#check fun b => foo.match_1 (fun _ => Bool) b (fun _ => false)

end WithFoo
