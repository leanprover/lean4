/-!
Functional induction: a `match` under an applied lambda, with a recursive call under `>>=`
(#15749). The induction hypothesis collected under the binder must not confuse `inferMatchType`.
-/

mutual
def f (xs : List Nat) (zs : List Nat) : Option Nat :=
  (fun (next : Unit → Option Nat) =>
    match xs with
    | _ :: rest => (some zs) >>= fun ys => g ys zs rest
    | _ => next ())
  (fun _ => none)
termination_by (sizeOf xs, 0)
def g (ys zs rest : List Nat) : Option Nat :=
  match ys with
  | _ :: more => g more zs rest
  | [] => f rest zs
termination_by (sizeOf rest, 1 + sizeOf ys)
end

/--
info: f.mutual_induct : ∀ (motive1 : List Nat → Prop) (motive2 : List Nat → List Nat → Prop),
  (∀ (xs : List Nat),
      (match xs with
        | head :: rest => ∀ (ys : List Nat), motive2 ys rest
        | x => True) →
        motive1 xs) →
    (∀ (rest : List Nat) (head : Nat) (more : List Nat), motive2 more rest → motive2 (head :: more) rest) →
      (∀ (rest : List Nat), motive1 rest → motive2 [] rest) →
        (∀ (xs : List Nat), motive1 xs) ∧ ∀ (ys rest : List Nat), motive2 ys rest
-/
#guard_msgs in
#check @f.mutual_induct
