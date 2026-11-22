/-!
Functional induction: a partially applied recursive call of a structurally recursive function
(e.g. `have g := f n`) is folded back to a call of the function, and provides an induction
hypothesis quantified over the missing arguments.
-/

def foo : (n : Nat) → (m : Nat) → Nat
  | 0, m => m
  | n+1, m => have f := foo n; f m
termination_by structural n => n

/--
info: foo.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n m : Nat), (∀ (m : Nat), motive n m) → motive n.succ m) (n m : Nat) : motive n m
-/
#guard_msgs in
#check foo.induct

/--
info: foo.induct_unfolding (motive : Nat → Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m m)
  (case2 :
    ∀ (n m : Nat),
      have f := foo n;
      (∀ (m : Nat), motive n m (foo n m)) → motive n.succ m (f m))
  (n m : Nat) : motive n m (foo n m)
-/
#guard_msgs in
#check foo.induct_unfolding

-- Like `BitVec.instDecidableForallBitVec`
def decAll : ∀ (n : Nat) (P : Fin (n+1) → Prop) [DecidablePred P], Decidable (∀ v, P v)
  | 0, _, _ => inferInstance
  | n + 1, _, _ =>
    have := decAll n
    inferInstance
termination_by structural n => n

/--
info: decAll.induct (motive : (n : Nat) → (P : Fin (n + 1) → Prop) → [DecidablePred P] → Prop)
  (case1 : ∀ (P : Fin (0 + 1) → Prop) (x : DecidablePred P), motive 0 P)
  (case2 :
    ∀ (n : Nat) (P : Fin (n.succ + 1) → Prop) (x : DecidablePred P),
      (∀ (P : Fin (n + 1) → Prop) [inst : DecidablePred P], motive n P) → motive n.succ P)
  (n : Nat) (P : Fin (n + 1) → Prop) [DecidablePred P] : motive n P
-/
#guard_msgs in
#check decAll.induct

/--
info: decAll.induct_unfolding
  (motive : (n : Nat) → (P : Fin (n + 1) → Prop) → [DecidablePred P] → Decidable (∀ (v : Fin (n + 1)), P v) → Prop)
  (case1 : ∀ (P : Fin (0 + 1) → Prop) (x : DecidablePred P), motive 0 P inferInstance)
  (case2 :
    ∀ (n : Nat) (P : Fin (n.succ + 1) → Prop) (x : DecidablePred P),
      (∀ (P : Fin (n + 1) → Prop) [inst : DecidablePred P], motive n P (decAll n P)) → motive n.succ P inferInstance)
  (n : Nat) (P : Fin (n + 1) → Prop) [DecidablePred P] : motive n P (decAll n P)
-/
#guard_msgs in
#check decAll.induct_unfolding

-- Well-founded recursion gives the same induction hypothesis
def baz : (n : Nat) → (m : Nat) → Nat
  | 0, m => m
  | n+1, m => have f := baz n; f m
termination_by n => n

/--
info: baz.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n m : Nat), (∀ (m : Nat), motive n m) → motive n.succ m) (n m : Nat) : motive n m
-/
#guard_msgs in
#check baz.induct

-- The recursive call can be a prefix of an application, if the function returns a function
def ret : Nat → Nat → Nat
  | 0 => id
  | n+1 => fun m => ret n (m+1)
termination_by structural n => n

/--
info: ret.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ) (a✝ : Nat) :
  motive a✝
-/
#guard_msgs in
#check ret.induct
