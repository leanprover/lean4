-- set_option trace.Meta.FunInd true

inductive S where
  | var (x : Nat)
  | cons (x : Nat) (s : S)

def S.eraseDup (s : S) : S :=
  match s with
  | .var x => .var x
  | .cons _ s =>
    let s' := s.eraseDup
    match s' with
    | .var y => var y
    | .cons y _ => var y


/--
info: theorem S.eraseDup.induct_unfolding : ∀ (motive : S → S → Prop),
  (∀ (x : Nat), motive (S.var x) (S.var x)) →
    (∀ (x : Nat) (s : S),
        have s' := s.eraseDup;
        ∀ (y : Nat), s' = S.var y → motive s s.eraseDup → motive (S.cons x s) (S.var y)) →
      (∀ (x : Nat) (s : S),
          have s' := s.eraseDup;
          ∀ (y : Nat) (s_1 : S), s' = S.cons y s_1 → motive s s.eraseDup → motive (S.cons x s) (S.var y)) →
        ∀ (s : S), motive s s.eraseDup
-/
#guard_msgs (pass trace, all) in
#print sig S.eraseDup.induct_unfolding

def S.eraseDup' (s : S) : S :=
  match s with
  | .var x => .var x
  | .cons _ s =>
    let s' := s.eraseDup'
    match s' with
    | .var y => var y
    | .cons y _ => .cons y s'

/--
info: theorem S.eraseDup'.induct_unfolding : ∀ (motive : S → S → Prop),
  (∀ (x : Nat), motive (S.var x) (S.var x)) →
    (∀ (x : Nat) (s : S),
        have s' := s.eraseDup';
        ∀ (y : Nat), s' = S.var y → motive s s.eraseDup' → motive (S.cons x s) (S.var y)) →
      (∀ (x : Nat) (s : S),
          have s' := s.eraseDup';
          ∀ (y : Nat) (s_1 : S), s' = S.cons y s_1 → motive s s.eraseDup' → motive (S.cons x s) (S.cons y s')) →
        ∀ (s : S), motive s s.eraseDup'
-/
#guard_msgs (pass trace, all) in
#print sig S.eraseDup'.induct_unfolding

def S.eraseDup'' (s : S) : S :=
  match s with
  | .var x => .var x
  | .cons _ s =>
    match s.eraseDup'' with
    | .var y => var y
    | .cons y _ => .var y

/--
info: theorem S.eraseDup''.induct_unfolding : ∀ (motive : S → S → Prop),
  (∀ (x : Nat), motive (S.var x) (S.var x)) →
    (∀ (x : Nat) (s : S) (y : Nat), s.eraseDup'' = S.var y → motive s s.eraseDup'' → motive (S.cons x s) (S.var y)) →
      (∀ (x : Nat) (s : S) (y : Nat) (s_1 : S),
          s.eraseDup'' = S.cons y s_1 → motive s s.eraseDup'' → motive (S.cons x s) (S.var y)) →
        ∀ (s : S), motive s s.eraseDup''
-/
#guard_msgs (pass trace, all) in
#print sig S.eraseDup''.induct_unfolding
