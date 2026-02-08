inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

-- set_option trace.split.failure true
-- set_option trace.split.debug true
-- set_option trace.Elab.definition.structural.eqns true

def decEqVecPlain {α} {a} [DecidableEq α] (x : @Vec α a) (x_1 : @Vec α a) : Decidable (x = x_1) :=
  if h : Vec.ctorIdx x = Vec.ctorIdx x_1 then
    match x, x_1, h with
    | Vec.nil, Vec.nil, _ => isTrue rfl
    | Vec.cons a_1 a_2, Vec.cons b b_1, _ =>
        if h_1 : @a_1 = @b then by
          subst h_1
          exact
            let inst := decEqVecPlain @a_2 @b_1;
            if h_2 : @a_2 = @b_1 then by subst h_2; exact isTrue rfl
            else isFalse (by intro n; injection n; apply h_2 _; assumption)
        else isFalse (by intro n_1; injection n_1; apply h_1 _; assumption)
  else isFalse (fun h' => h (congrArg Vec.ctorIdx h'))
termination_by structural x

-- Splitter and eqns generated just fine
#guard_msgs(drop info) in
#print sig decEqVecPlain.match_1
#guard_msgs(drop info) in
#print sig decEqVecPlain.match_1.eq_1

/--
info: theorem decEqVecPlain.eq_def.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : DecidableEq α] (x x_1 : Vec α a),
  decEqVecPlain x x_1 =
    if h : x.ctorIdx = x_1.ctorIdx then
      match a, x, x_1, h with
      | .(0), Vec.nil, Vec.nil, x => isTrue ⋯
      | .(n + 1), Vec.cons a_1 a_2, Vec.cons b b_1, x =>
        if h_1 : a_1 = b then
          Eq.ndrec (motive := fun b =>
            (Vec.cons a_1 a_2).ctorIdx = (Vec.cons b b_1).ctorIdx → Decidable (Vec.cons a_1 a_2 = Vec.cons b b_1))
            (fun x =>
              have inst_1 := decEqVecPlain a_2 b_1;
              if h_2 : a_2 = b_1 then
                Eq.ndrec (motive := fun b_1 =>
                  (Vec.cons a_1 a_2).ctorIdx = (Vec.cons a_1 b_1).ctorIdx →
                    have inst := decEqVecPlain a_2 b_1;
                    Decidable (Vec.cons a_1 a_2 = Vec.cons a_1 b_1))
                  (fun x =>
                    have inst := decEqVecPlain a_2 a_2;
                    isTrue ⋯)
                  h_2 x
              else isFalse ⋯)
            h_1 x
        else isFalse ⋯
    else isFalse ⋯
-/
#guard_msgs(pass trace, all) in
#print sig decEqVecPlain.eq_def


axiom testSorry : α

inductive I : Nat → Type u | cons : I n → I (n + 1)
axiom P : I n → Prop
@[instance] axiom instDecEqI : ∀ (x : I n), Decidable (P x)
axiom R : I n → Type
set_option trace.split.failure true in
noncomputable def foo (x x' : I n) : R x :=
 if h : P x then
 match (generalizing := false) x, x', id h with --NB: non-FVar discr
 | .cons a_2, .cons a_2', _ => (testSorry : _ → _ → _) (foo a_2 a_2') h
 else testSorry
termination_by structural x


/--
info: theorem foo.eq_def.{u_1, u_2} : ∀ {n : Nat} (x : I n) (x' : I n),
  foo x x' =
    if h : P x then
      match n, x, x', ⋯ with
      | .(n_1 + 1), a_2.cons, a_2'.cons, x_1 => testSorry (foo a_2 a_2') h
    else testSorry
-/
#guard_msgs(pass trace, all) in
#print sig foo.eq_def
