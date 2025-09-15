inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

set_option trace.split.failure true
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

-- Some theorem that lets us try split

-- Simple case that seems to work
example :
  decEqVecPlain.match_1 (motive := fun _ _ _ _ => Nat) n x1 x2 h (fun _ => 0) (fun _ _ _ _ _ _ => 1) = x1.ctorIdx := by
  split <;> rfl

-- This case also seems to work
theorem decEqVecPlain.match_1_cases
  (motive : (n : Nat) → (x1 x2 : Vec α n) → Sort u)
  (anil : motive 0 Vec.nil Vec.nil)
  (acons : ∀ n a1 as1 b1 bs1, motive (n + 1) (Vec.cons a1 as1) (Vec.cons b1 bs1))
  (P : (n : Nat) → (x1 x2 : Vec α n) → (m : motive n x1 x2) → Prop)
  (hnil : P 0 Vec.nil Vec.nil anil)
  (hcons : ∀ n a1 as1 b1 bs1, P (n + 1) (Vec.cons a1 as1) (Vec.cons b1 bs1) (acons n a1 as1 b1 bs1))  :
  P n x1 x2 (decEqVecPlain.match_1 (motive := fun n x1 x2 _ => motive n x1 x2) n x1 x2 h
    (fun _ => anil) (@fun a1 n as1 b1 bs1 _ => @acons n a1 as1 b1 bs1)) := by
  split
  · apply hnil
  · apply hcons

-- So why does this split not work?

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
---
trace: [split.failure] `split` tactic failed to generalize discriminant(s) at
      match (motive :=
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
                  (Vec.cons a_1 a_2).ctorIdx = (Vec.cons a_1 x).ctorIdx → Decidable (Vec.cons a_1 a_2 = Vec.cons a_1 x))
                  (fun x => isTrue ⋯) h_2 x
              else isFalse ⋯)
            ⋯ x
        else isFalse ⋯
    resulting expression was not type correct
    possible solution: generalize discriminant(s) manually before using `split`
[split.failure] `split` tactic failed to generalize discriminant(s) at
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
    resulting expression was not type correct
    possible solution: generalize discriminant(s) manually before using `split`
-/
#guard_msgs in
#print sig decEqVecPlain.eq_def

-- Nonrecursive

inductive Vec' (α : Type u) : Nat → Type u
  | nil  : Vec' α 0
  | cons : α → {n : Nat} → Vec' α (n+1)

set_option trace.split.failure true

def decEqVec' {α} {a} [DecidableEq α] (x : @Vec' α a) (x_1 : @Vec' α a) : Decidable (x = x_1) :=
  if h : x.ctorIdx = x_1.ctorIdx then
    match x, x_1, h with
    | .nil, .nil, _ => isTrue rfl
    | .cons a_1, .cons b, _ =>
        if h_1 : @a_1 = @b then by
          subst h_1
          exact
            isTrue rfl
        else isFalse (by intro n_1; injection n_1; apply h_1 _; assumption)
  else isFalse (fun h' => h (congrArg Vec'.ctorIdx h'))

-- Splitter and eqns generated just fine
#guard_msgs(drop info) in
#print sig decEqVec'.match_1
#guard_msgs(drop info) in
#print sig decEqVec'.match_1.eq_1

-- Some theorem that lets us try split

-- Simple case that seems to work
example :
  decEqVec'.match_1 (motive := fun _ _ _ _ => Nat) n x1 x2 h (fun _ => 0) (fun _ _ _ _ => 1) = x1.ctorIdx := by
  split <;> rfl

-- This case also seems to work
theorem decEqVec'.match_1_cases
  (motive : (n : Nat) → (x1 x2 : Vec' α n) → Sort u)
  (anil : motive 0 Vec'.nil Vec'.nil)
  (acons : ∀ n a1 b1, motive (n + 1) (Vec'.cons a1) (Vec'.cons b1))
  (P : (n : Nat) → (x1 x2 : Vec' α n) → (m : motive n x1 x2) → Prop)
  (hnil : P 0 Vec'.nil Vec'.nil anil)
  (hcons : ∀ n a1 b1, P (n + 1) (Vec'.cons a1) (Vec'.cons b1) (acons n a1 b1))  :
  P n x1 x2 (decEqVec'.match_1 (motive := fun n x1 x2 _ => motive n x1 x2) n x1 x2 h
    (fun _ => anil) (@fun a1 n b1 _ => @acons n a1 b1)) := by
  split
  · apply hnil
  · apply hcons
