/-!
Induction hypotheses collected in one function's case of a mutual structural recursion
must not leak into the cases of the other functions.
-/

mutual
inductive A where
  | base
  | wrap (b : B)
inductive B where
  | base
  | wrap (a : A)
end

mutual
def f (a : A) : Nat := Nat.succ (match a with | .wrap b => g b | _ => 0)
termination_by structural a
def g (b : B) : Nat := match b with | .wrap a => f a | _ => 0
termination_by structural b
end

/--
info: f.mutual_induct (motive_1 : A → Prop) (motive_2 : B → Prop)
  (case1 :
    ∀ (t : A),
      (match t with
        | A.wrap b => motive_2 b
        | x => True) →
        motive_1 t)
  (case2 : ∀ (a : A), motive_1 a → motive_2 (B.wrap a))
  (case3 : ∀ (t : B), (∀ (a : A), t = B.wrap a → False) → motive_2 t) : (∀ (a : A), motive_1 a) ∧ ∀ (b : B), motive_2 b
-/
#guard_msgs in
#check f.mutual_induct

-- Same argument type, so both functions share a minor premise (split via `PProd.mk`)
namespace SameType
mutual
def f (n : Nat) : Nat := Nat.succ (match n with | n+1 => g n | _ => 0)
termination_by structural n
def g (n : Nat) : Nat := match n with | n+1 => f n | _ => 0
termination_by structural n
end

/--
info: SameType.f.mutual_induct (motive_1 motive_2 : Nat → Prop)
  (case1 :
    ∀ (t : Nat),
      (match t with
        | n.succ => motive_2 n
        | x => True) →
        motive_1 t)
  (case2 : ∀ (n : Nat), motive_1 n → motive_2 n.succ)
  (case3 : ∀ (t : Nat), (∀ (n : Nat), t = n.succ → False) → motive_2 t) :
  (∀ (n : Nat), motive_1 n) ∧ ∀ (n : Nat), motive_2 n
-/
#guard_msgs in
#check f.mutual_induct
end SameType
