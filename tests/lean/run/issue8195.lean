import Lean

-- set_option trace.Meta.FunInd true

axiom testSorry : α

def test (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match x == 3 with
    | false => test l
    | true => test l

/--
info: test.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 : ∀ (x : Nat) (l : List Nat), (x == 3) = false → motive l (test l) → motive (x :: l) (test l))
  (case3 : ∀ (x : Nat) (l : List Nat), (x == 3) = true → motive l (test l) → motive (x :: l) (test l)) (l : List Nat) :
  motive l (test l)
-/
#guard_msgs in
#check test.induct_unfolding

opaque someFunction (x : Nat) (h : (x == 3) = false) : Nat
opaque someOtherFunction (x : Nat) (h : (x == 3) = true) : Nat

def deptest (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match h : x == 3 with
    | false => deptest l + someFunction x h
    | true => deptest l + someOtherFunction x h

/--
info: deptest.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat) (h : (x == 3) = false),
      motive l (deptest l) → motive (x :: l) (deptest l + someFunction x h))
  (case3 :
    ∀ (x : Nat) (l : List Nat) (h : (x == 3) = true),
      motive l (deptest l) → motive (x :: l) (deptest l + someOtherFunction x h))
  (l : List Nat) : motive l (deptest l)
-/
#guard_msgs in
#check deptest.induct_unfolding

def depTestOddType (l : List Nat) :
    match l with
    | [] => Unit
    | x :: _ =>
      if x == 3 then
        Unit
      else
        Nat
  :=
  match l with
  | [] => ()
  | x :: _ =>
    (match h : x == 3 with
    | false => someFunction x h
    | true => () : if x == 3 then Unit else Nat)

def myTest {α}
  (mmotive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : mmotive x :=
  match (generalizing := false) h : x with
  | (a :: dc) => h_1 a dc h
  | x' => h_2 x' h

-- set_option trace.Meta.Match.matchEqs true in
run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``myTest.match_1

-- #check myTest.match_1
/--
info: myTest.match_1.splitter.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc))
  (h_2 : (x' : List α) → (∀ (a : α) (dc : List α), x' = a :: dc → False) → x✝ = x' → motive x') : motive x✝
-/
#guard_msgs in
#check myTest.match_1.splitter
/--
info: myTest.match_1.gen_eq_1.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x') (a : α)
  (dc : List α) (heq_1 : x✝ = a :: dc) :
  HEq
    (match h : x✝ with
    | a :: dc => h_1 a dc h
    | x' => h_2 x' h)
    (h_1 a dc heq_1)
-/
#guard_msgs in
#check myTest.match_1.gen_eq_1

/--
info: myTest.match_1.gen_eq_2.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x')
  (x' : List α) (heq_1 : x✝ = x') :
  (∀ (a : α) (dc : List α), x' = a :: dc → False) →
    HEq
      (match h : x✝ with
      | a :: dc => h_1 a dc h
      | x' => h_2 x' h)
      (h_2 x' heq_1)
-/
#guard_msgs in
#check myTest.match_1.gen_eq_2


def take (n : Nat) (xs : List α) : List α := match n, xs with
  | 0,   _     => []
  | _+1, []    => []
  | n+1, a::as => a :: take n as

/--
info: take.match_1.{u_1, u_2} {α : Type u_1} (motive : Nat → List α → Sort u_2) (n✝ : Nat) (xs✝ : List α)
  (h_1 : (x : List α) → motive 0 x) (h_2 : (n : Nat) → motive n.succ [])
  (h_3 : (n : Nat) → (a : α) → (as : List α) → motive n.succ (a :: as)) : motive n✝ xs✝
-/
#guard_msgs in
#check take.match_1

-- set_option trace.Meta.Match.matchEqs true in
run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``take.match_1

/--
info: take.match_1.gen_eq_1.{u_1, u_2} {α : Type u_1} (motive : Nat → List α → Sort u_2) (n✝ : Nat) (xs✝ : List α)
  (h_1 : (x : List α) → motive 0 x) (h_2 : (n : Nat) → motive n.succ [])
  (h_3 : (n : Nat) → (a : α) → (as : List α) → motive n.succ (a :: as)) (x✝ : List α) (heq_1 : n✝ = 0)
  (heq_2 : xs✝ = x✝) :
  HEq
    (match n✝, xs✝ with
    | 0, x => h_1 x
    | n.succ, [] => h_2 n
    | n.succ, a :: as => h_3 n a as)
    (h_1 x✝)
-/
#guard_msgs in #check take.match_1.gen_eq_1

def matchOptionUnit (o? : Option Unit) : Bool := Id.run do
    if let some _ := o? then
      true
    else
      false

run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``matchOptionUnit.match_1

/--
info: matchOptionUnit.match_1.gen_eq_1.{u_1} (motive : Option Unit → Sort u_1) (o?✝ : Option Unit)
  (h_1 : (val : Unit) → motive (some val)) (h_2 : (x : Option Unit) → motive x) (val✝ : Unit)
  (heq_1 : o?✝ = some val✝) :
  HEq
    (match o?✝ with
    | some val => h_1 ()
    | x => h_2 x)
    (h_1 val✝)
-/
#guard_msgs in
#check matchOptionUnit.match_1.gen_eq_1

run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``Std.Tactic.BVDecide.BVExpr.bitblast.go.match_5

set_option linter.unusedVariables false in
private partial def utf16PosToCodepointPosFromAux (s : String) : Nat → String.Pos → Nat → Bool
  | 0,        _,       cp => true
  | utf16pos, utf8pos, cp => false

run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``utf16PosToCodepointPosFromAux.match_1

axiom some_expr : Option Nat
def wrongEq (m? : Option Nat) (h : some_expr = m?)
  (w : 0 < m?.getD 0) : Bool := by
  match m?, w with
  | some m?, _ => exact true

run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``wrongEq.match_1

set_option linter.unusedVariables false in
noncomputable def myNamedPatternTest (x : List Bool) : Bool :=
  match hx : x with
  | x'@hx':(x::xs) => false
  | x' => true

run_meta do let _ ← Lean.Tactic.FunInd.Match.genGeneralizedMatchEqns ``myNamedPatternTest.match_1

/--
info: myNamedPatternTest.match_1.gen_eq_1.{u_1} (motive : List Bool → Sort u_1) (x✝ : List Bool)
  (h_1 : (x' : List Bool) → (x : Bool) → (xs : List Bool) → x' = x :: xs → x✝ = x :: xs → motive (x :: xs))
  (h_2 : (x' : List Bool) → x✝ = x' → motive x') (x : Bool) (xs : List Bool) (heq_1 : x✝ = x :: xs) :
  HEq
    (match hx : x✝ with
    | x'@hx':(x :: xs) => h_1 x' x xs hx' hx
    | x' => h_2 x' hx)
    (h_1 (x :: xs) x xs ⋯ heq_1)
-/
#guard_msgs in
#check myNamedPatternTest.match_1.gen_eq_1

#exit
run_meta do
  let s := Lean.Meta.Match.Extension.extension.getState (← getEnv) (asyncMode := .local)
  for (k,_) in s.map do --, _ in [:600] do
    unless (`Lean).isPrefixOf (privateToUserName k) do
      let mut ok := false
      try
        let _ ← Match.getEquationsFor k
        ok := true
      catch _ =>
        pure ()
      if ok then
        try
          let _ ← genGeneralizedMatchEqns k
        catch e =>
          logInfo m!"failed to generate equations for {k} in {.ofConstName k.getPrefix}\n{indentD e.toMessageData}"
