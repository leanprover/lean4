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
error: Failed to realize constant decEqVecPlain.eq_def:
  failed to generate equational theorem for `decEqVecPlain`
  case nil.isTrue
  α : Type u_1
  inst : DecidableEq α
  x_1 : Vec α 0
  h✝ : Vec.nil.ctorIdx = x_1.ctorIdx
  ⊢ (match (motive :=
          (a : Nat) →
            (x x_1 : Vec α a) →
              x.ctorIdx = x_1.ctorIdx →
                Vec.rec PUnit (fun a {n} a_1 a_ih => ((x_1 : Vec α n) → Decidable (a_1 = x_1)) ×' a_ih) x →
                  Decidable (x = x_1))
          0, Vec.nil, x_1, ⋯ with
        | .(0), Vec.nil, Vec.nil, x => fun x => isTrue ⋯
        | .(n + 1), Vec.cons a_1 a_2, Vec.cons b b_1, x => fun x_2 =>
          if h : a_1 = b then
            Eq.rec (motive := fun x x_3 =>
              (Vec.cons a_1 a_2).ctorIdx = (Vec.cons x b_1).ctorIdx → Decidable (Vec.cons a_1 a_2 = Vec.cons x b_1))
              (fun x =>
                if h_2 : a_2 = b_1 then
                  Eq.rec (motive := fun x x_3 =>
                    (Vec.cons a_1 a_2).ctorIdx = (Vec.cons a_1 x).ctorIdx →
                      Decidable (Vec.cons a_1 a_2 = Vec.cons a_1 x))
                    (fun x => isTrue ⋯) h_2 x
                else isFalse ⋯)
              ⋯ x
          else isFalse ⋯)
        PUnit.unit =
      match 0, Vec.nil, x_1, ⋯ with
      | .(0), Vec.nil, Vec.nil, x => isTrue ⋯
      | .(n + 1), Vec.cons a_1 a_2, Vec.cons b b_1, x =>
        if h : a_1 = b then
          Eq.rec (motive := fun x x_2 =>
            (Vec.cons a_1 a_2).ctorIdx = (Vec.cons x b_1).ctorIdx → Decidable (Vec.cons a_1 a_2 = Vec.cons x b_1))
            (fun x =>
              if h_2 : a_2 = b_1 then
                Eq.rec (motive := fun x x_2 =>
                  (Vec.cons a_1 a_2).ctorIdx = (Vec.cons a_1 x).ctorIdx → Decidable (Vec.cons a_1 a_2 = Vec.cons a_1 x))
                  (fun x => isTrue ⋯) h_2 x
              else isFalse ⋯)
            ⋯ x
        else isFalse ⋯
---
error: Unknown constant `decEqVecPlain.eq_def`
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
error: Failed to realize constant foo.eq_def:
  failed to generate equational theorem for `foo`
  case isTrue
  n_1 : Nat
  a : I n_1
  x' : I (n_1 + 1)
  h✝ : P a.cons
  ⊢ (match (motive := (n : Nat) → (x : I n) → I n → P x → I.rec (fun {n} a a_ih => (I n → R a) ×' a_ih) x → R x)
          n_1 + 1, a.cons, x', ⋯ with
        | .(n + 1), a_2.cons, a_2'.cons, x => fun x => testSorry (x.1 a_2') h✝)
        (I.rec
          (fun {n} a a_ih =>
            ⟨fun x' =>
              if h : P a.cons then
                (match (motive :=
                    (n : Nat) → (x : I n) → I n → P x → I.rec (fun {n} a a_ih => (I n → R a) ×' a_ih) x → R x) n + 1,
                    a.cons, x', ⋯ with
                  | .(n_2 + 1), a_2.cons, a_2'.cons, x => fun x => testSorry (x.1 a_2') h)
                  a_ih
              else testSorry,
              a_ih⟩)
          a) =
      match n_1 + 1, a.cons, x', ⋯ with
      | .(n + 1), a_2.cons, a_2'.cons, x => testSorry (foo a_2 a_2') h✝
---
error: Unknown constant `foo.eq_def`
-/
#guard_msgs(pass trace, all) in
#print sig foo.eq_def


noncomputable def nondep (x x' : I n) : Bool :=
 if h : P x then
 match (generalizing := false) x, x', id h with --NB: non-FVar discr
 | .cons a_2, .cons a_2', _ => nondep a_2 a_2'
 else false
termination_by structural x

/--
error: Failed to realize constant nondep.eq_def:
  failed to generate equational theorem for `nondep`
  case h_1
  n_1 : Nat
  a : I n_1
  x' : I (n_1 + 1)
  h✝ x✝ : P a.cons
  n : Nat
  x : I n
  x'_1 : I n
  x_1 : P x
  n_2 : Nat
  a_2 : I n_2
  a_2' : I n_2
  x_2 : P a_2.cons
  heq✝³ : n_1 + 1 = n_2 + 1
  heq✝² : a.cons ≍ a_2.cons
  heq✝¹ : x' ≍ a_2'.cons
  heq✝ : x✝ ≍ x_2
  ⊢ (match (motive := (n : Nat) → (x : I n) → I n → P x → I.rec (fun {n} a a_ih => (I n → Bool) ×' a_ih) x → Bool)
          n_1 + 1, a.cons, x', x✝ with
        | .(n + 1), a_2.cons, a_2'.cons, x => fun x => x.1 a_2')
        (I.rec
          (fun {n} a a_ih =>
            ⟨fun x' =>
              if h : P a.cons then
                (match (motive :=
                    (n : Nat) → (x : I n) → I n → P x → I.rec (fun {n} a a_ih => (I n → Bool) ×' a_ih) x → Bool) n + 1,
                    a.cons, x', ⋯ with
                  | .(n + 1), a_2.cons, a_2'.cons, x => fun x => x.1 a_2')
                  a_ih
              else false,
              a_ih⟩)
          a) =
      (I.rec
            (fun {n} a a_ih =>
              ⟨fun x' =>
                if h : P a.cons then
                  (match (motive :=
                      (n : Nat) → (x : I n) → I n → P x → I.rec (fun {n} a a_ih => (I n → Bool) ×' a_ih) x → Bool)
                      n + 1, a.cons, x', ⋯ with
                    | .(n + 1), a_2.cons, a_2'.cons, x => fun x => x.1 a_2')
                    a_ih
                else false,
                a_ih⟩)
            a_2).1
        a_2'
---
error: Unknown constant `nondep.eq_def`
-/
#guard_msgs in
#print sig nondep.eq_def
