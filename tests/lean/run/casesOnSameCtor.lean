import Lean

/-! This tests and documents the constructions in CasesOnSameCtor. -/

open Lean Meta

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

namespace Vec

-- set_option debug.skipKernelTC true
run_meta mkCasesOnSameCtor `Vec.match_on_same_ctor ``Vec

/--
info: Vec.match_on_same_ctor.het.{u_1, u} {α : Type u} {motive : {a : Nat} → Vec α a → {a : Nat} → Vec α a → Sort u_1}
  {a✝ : Nat} (t : Vec α a✝) {a✝¹ : Nat} (t✝ : Vec α a✝¹) (h : t.ctorIdx = t✝.ctorIdx) (nil : motive nil nil)
  (cons :
    (a : α) →
      {n : Nat} → (a_1 : Vec α n) → (a_2 : α) → {n_1 : Nat} → (a_3 : Vec α n_1) → motive (cons a a_1) (cons a_2 a_3)) :
  motive t t✝
-/
#guard_msgs in
#check Vec.match_on_same_ctor.het

/--
info: Vec.match_on_same_ctor.{u_1, u} {α : Type u}
  {motive : {a : Nat} → (t t_1 : Vec α a) → t.ctorIdx = t_1.ctorIdx → Sort u_1} {a✝ : Nat} (t t✝ : Vec α a✝)
  (h : t.ctorIdx = t✝.ctorIdx) (nil : Unit → motive nil nil ⋯)
  (cons : (a : α) → {n : Nat} → (a_1 : Vec α n) → (a' : α) → (a'_1 : Vec α n) → motive (cons a a_1) (cons a' a'_1) ⋯) :
  motive t t✝ h
-/
#guard_msgs in
#check Vec.match_on_same_ctor

-- Splitter and equations are generated
/--
info: Vec.match_on_same_ctor.splitter.{u_1, u} {α : Type u}
  {motive : {a : Nat} → (t t_1 : Vec α a) → t.ctorIdx = t_1.ctorIdx → Sort u_1} {a✝ : Nat} (t t✝ : Vec α a✝)
  (h : t.ctorIdx = t✝.ctorIdx) (nil : Unit → motive nil nil ⋯)
  (cons : (a : α) → {n : Nat} → (a_1 : Vec α n) → (a' : α) → (a'_1 : Vec α n) → motive (cons a a_1) (cons a' a'_1) ⋯) :
  motive t t✝ h
-/
#guard_msgs in
#check Vec.match_on_same_ctor.splitter

-- After #11211 this is no longer true. Should we thunk the same-ctor-construction?

-- -- Since there is no overlap, the splitter is equal to the matcher
-- -- (I wonder if we should use this in general in MatchEq)
-- example : @Vec.match_on_same_ctor = @Vec.match_on_same_ctor.splitter := by rfl

/--
info: Vec.match_on_same_ctor.eq_2.{u_1, u} {α : Type u}
  {motive : {a : Nat} → (t t_1 : Vec α a) → t.ctorIdx = t_1.ctorIdx → Sort u_1} (a✝ : α) (n : Nat) (a✝¹ : Vec α n)
  (a'✝ : α) (a'✝¹ : Vec α n) (nil : Unit → motive nil nil ⋯)
  (cons : (a : α) → {n : Nat} → (a_1 : Vec α n) → (a' : α) → (a'_1 : Vec α n) → motive (cons a a_1) (cons a' a'_1) ⋯) :
  (match n + 1, Vec.cons a✝ a✝¹, Vec.cons a'✝ a'✝¹ with
    | 0, Vec.nil, Vec.nil, ⋯ => nil ()
    | n + 1, Vec.cons a a_1, Vec.cons a' a'_1, ⋯ => cons a a_1 a' a'_1) =
    cons a✝ a✝¹ a'✝ a'✝¹
-/
#guard_msgs in
#check Vec.match_on_same_ctor.eq_2

-- Recursion works

-- set_option trace.split.debug true
-- set_option trace.split.failure true
-- set_option trace.Elab.definition.structural.eqns true

def decEqVec {α} {a} [DecidableEq α] (x : @Vec α a) (x_1 : @Vec α a) : Decidable (x = x_1) :=
  if h : Vec.ctorIdx x = Vec.ctorIdx x_1 then
    Vec.match_on_same_ctor x x_1 h (fun _ => isTrue rfl)
      @fun a_1 _ a_2 b b_1 =>
        if h_1 : @a_1 = @b then by
          subst h_1
          exact
            let inst := decEqVec @a_2 @b_1;
            if h_2 : @a_2 = @b_1 then by subst h_2; exact isTrue rfl
            else isFalse (by intro n; injection n; apply h_2 _; assumption)
        else isFalse (by intro n_1; injection n_1; apply h_1 _; assumption)
  else isFalse (fun h' => h (congrArg Vec.ctorIdx h'))
termination_by structural x


-- Equation generation and pretty match syntax:

/--
info: theorem Vec.decEqVec.eq_def.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : DecidableEq α] (x x_1 : Vec α a),
  x.decEqVec x_1 =
    if h : x.ctorIdx = x_1.ctorIdx then
      match a, x, x_1 with
      | 0, Vec.nil, Vec.nil, ⋯ => isTrue ⋯
      | x + 1, Vec.cons a_1 a_2, Vec.cons b b_1, ⋯ =>
        if h_1 : a_1 = b then
          h_1 ▸
            have inst_1 := a_2.decEqVec b_1;
            if h_2 : a_2 = b_1 then
              h_2 ▸
                have inst := a_2.decEqVec a_2;
                isTrue ⋯
            else isFalse ⋯
        else isFalse ⋯
    else isFalse ⋯
-/
#guard_msgs(pass trace, all) in
#print sig decEqVec.eq_def


-- Incidentially, normal match syntax is able to produce an equivalent matcher
-- (with different implementation):
-- (see #10195 for problems with equation generation)

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
end Vec

namespace List
-- set_option debug.skipKernelTC true
-- set_option trace.compiler.ir.result true

run_meta mkCasesOnSameCtor `List.match_on_same_ctor ``List

/--
info: List.match_on_same_ctor.{u_1, u} {α : Type u} {motive : (t t_1 : List α) → t.ctorIdx = t_1.ctorIdx → Sort u_1}
  (t t✝ : List α) (h : t.ctorIdx = t✝.ctorIdx) (nil : Unit → motive [] [] ⋯)
  (cons : (head : α) → (tail : List α) → (head' : α) → (tail' : List α) → motive (head :: tail) (head' :: tail') ⋯) :
  motive t t✝ h
-/
#guard_msgs in
#check List.match_on_same_ctor

end List

namespace BadIdx
opaque f : Nat → Nat
inductive T : (n : Nat) → Type where
  | mk1 : Fin n → T (f n)
  | mk2 : Fin (2*n) → T (f n)

run_meta mkCasesOnSameCtorHet `BadIdx.casesOn2Het ``T
/--
error: Dependent elimination failed: Failed to solve equation
  f n✝ = f n
-/
#guard_msgs in
run_meta mkCasesOnSameCtor `BadIdx.casesOn2 ``T

end BadIdx
