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
  (∀ (y : Nat), motive (S.var y) (S.var y)) →
    (∀ (y : Nat) (s : S),
        have s' := s.eraseDup;
        ∀ (y_1 : Nat), s' = S.var y_1 → motive s s.eraseDup → motive (S.cons y s) (S.var y_1)) →
      (∀ (y : Nat) (s : S),
          have s' := s.eraseDup;
          ∀ (y_1 : Nat) (s_1 : S), s' = S.cons y_1 s_1 → motive s s.eraseDup → motive (S.cons y s) (S.var y_1)) →
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
  (∀ (y : Nat), motive (S.var y) (S.var y)) →
    (∀ (y : Nat) (s : S),
        have s' := s.eraseDup';
        ∀ (y_1 : Nat), s' = S.var y_1 → motive s s.eraseDup' → motive (S.cons y s) (S.var y_1)) →
      (∀ (y : Nat) (s : S),
          have s' := s.eraseDup';
          ∀ (y_1 : Nat) (s_1 : S), s' = S.cons y_1 s_1 → motive s s.eraseDup' → motive (S.cons y s) (S.cons y_1 s')) →
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
  (∀ (y : Nat), motive (S.var y) (S.var y)) →
    (∀ (y : Nat) (s : S) (y_1 : Nat),
        s.eraseDup'' = S.var y_1 → motive s s.eraseDup'' → motive (S.cons y s) (S.var y_1)) →
      (∀ (y : Nat) (s : S) (y_1 : Nat) (s_1 : S),
          s.eraseDup'' = S.cons y_1 s_1 → motive s s.eraseDup'' → motive (S.cons y s) (S.var y_1)) →
        ∀ (s : S), motive s s.eraseDup''
-/
#guard_msgs (pass trace, all) in
#print sig S.eraseDup''.induct_unfolding
