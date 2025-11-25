/-!
Tricky cases and regressions tests for generalized match equations.
-/
-- set_option trace.Meta.Match.matchEqs true

def myTest {α}
  (mmotive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : mmotive x :=
  match (generalizing := false) h : x with
  | (a :: dc) => h_1 a dc h
  | x' => h_2 x' h

-- #check myTest.match_1
/--
info: myTest.match_1.splitter.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc))
  (h_2 : (x' : List α) → (∀ (a : α) (dc : List α), x' = a :: dc → False) → x✝ = x' → motive x') : motive x✝
-/
#guard_msgs(pass trace, all) in
#check myTest.match_1.splitter
/--
info: myTest.match_1.congr_eq_1.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x') (a : α)
  (dc : List α) (heq_1 : x✝ = a :: dc) :
  (match h : x✝ with
    | a :: dc => h_1 a dc h
    | x' => h_2 x' h) ≍
    h_1 a dc heq_1
-/
#guard_msgs(pass trace, all) in
#check myTest.match_1.congr_eq_1

/--
info: myTest.match_1.congr_eq_2.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x')
  (x' : List α) (heq_1 : x✝ = x') :
  (∀ (a : α) (dc : List α), x' = a :: dc → False) →
    (match h : x✝ with
      | a :: dc => h_1 a dc h
      | x' => h_2 x' h) ≍
      h_2 x' heq_1
-/
#guard_msgs(pass trace, all) in
#check myTest.match_1.congr_eq_2


def take (n : Nat) (xs : List α) : List α := match n, xs with
  | 0,   _     => []
  | _+1, []    => []
  | n+1, a::as => a :: take n as

/--
info: take.match_1.{u_1, u_2} {α : Type u_1} (motive : Nat → List α → Sort u_2) (n✝ : Nat) (xs✝ : List α)
  (h_1 : (x : List α) → motive 0 x) (h_2 : (n : Nat) → motive n.succ [])
  (h_3 : (n : Nat) → (a : α) → (as : List α) → motive n.succ (a :: as)) : motive n✝ xs✝
-/
#guard_msgs(pass trace, all) in
#check take.match_1

/--
info: take.match_1.congr_eq_1.{u_1, u_2} {α : Type u_1} (motive : Nat → List α → Sort u_2) (n✝ : Nat) (xs✝ : List α)
  (h_1 : (x : List α) → motive 0 x) (h_2 : (n : Nat) → motive n.succ [])
  (h_3 : (n : Nat) → (a : α) → (as : List α) → motive n.succ (a :: as)) (x✝ : List α) (heq_1 : n✝ = 0)
  (heq_2 : xs✝ = x✝) :
  (match n✝, xs✝ with
    | 0, x => h_1 x
    | n.succ, [] => h_2 n
    | n.succ, a :: as => h_3 n a as) ≍
    h_1 x✝
-/
#guard_msgs(pass trace, all) in #check take.match_1.congr_eq_1

def matchOptionUnit (o? : Option Unit) : Bool := Id.run do
    if let some _ := o? then
      true
    else
      false

/--
info: matchOptionUnit.match_1.congr_eq_1.{u_1} (motive : Option Unit → Sort u_1) (o?✝ : Option Unit)
  (h_1 : (val : Unit) → motive (some val)) (h_2 : (x : Option Unit) → motive x) (val✝ : Unit)
  (heq_1 : o?✝ = some val✝) :
  (match o?✝ with
    | some val => h_1 ()
    | x => h_2 x) ≍
    h_1 val✝
-/
#guard_msgs(pass trace, all) in
#check matchOptionUnit.match_1.congr_eq_1

set_option linter.unusedVariables false in
partial def utf16PosToCodepointPosFromAux (s : String) : Nat → String.Pos.Raw → Nat → Bool
  | 0,        _,       cp => true
  | utf16pos, utf8pos, cp => false

/--
info: utf16PosToCodepointPosFromAux.match_1.congr_eq_1.{u_1} (motive : Nat → String.Pos.Raw → Nat → Sort u_1) (x✝ : Nat)
  (x✝¹ : String.Pos.Raw) (x✝² : Nat) (h_1 : (x : String.Pos.Raw) → (cp : Nat) → motive 0 x cp)
  (h_2 : (utf16pos : Nat) → (utf8pos : String.Pos.Raw) → (cp : Nat) → motive utf16pos utf8pos cp) (x✝³ : String.Pos.Raw)
  (cp : Nat) (heq_1 : x✝ = 0) (heq_2 : x✝¹ = x✝³) (heq_3 : x✝² = cp) :
  (match x✝, x✝¹, x✝² with
    | 0, x, cp => h_1 x cp
    | utf16pos, utf8pos, cp => h_2 utf16pos utf8pos cp) ≍
    h_1 x✝³ cp
-/
#guard_msgs(pass trace, all) in
#check utf16PosToCodepointPosFromAux.match_1.congr_eq_1

opaque some_expr : Option Nat
def wrongEq (m? : Option Nat) (h : some_expr = m?)
  (w : 0 < m?.getD 0) : Bool := by
  match m?, w with
  | some m?, _ => exact true

/--
info: wrongEq.match_1.congr_eq_1.{u_1} (motive : (m? : Option Nat) → 0 < m?.getD 0 → some_expr = m? → Sort u_1)
  (m?✝ : Option Nat) (w✝ : 0 < m?✝.getD 0) (h : some_expr = m?✝)
  (h_1 : (m? : Nat) → (x : 0 < (some m?).getD 0) → (h : some_expr = some m?) → motive (some m?) x h) (m? : Nat)
  (x✝ : 0 < (some m?).getD 0) (h✝ : some_expr = some m?) (heq_1 : m?✝ = some m?) (heq_2 : w✝ ≍ x✝) (heq_3 : h ≍ h✝) :
  (match m?✝, w✝, h with
    | some m?, x, h => h_1 m? x h) ≍
    h_1 m? x✝ h✝
-/
#guard_msgs(pass trace, all) in #check wrongEq.match_1.congr_eq_1

set_option linter.unusedVariables false in
noncomputable def myNamedPatternTest (x : List Bool) : Bool :=
  match hx : x with
  | x'@hx':(x::xs) => false
  | x' => true

/--
info: myNamedPatternTest.match_1.congr_eq_1.{u_1} (motive : List Bool → Sort u_1) (x✝ : List Bool)
  (h_1 : (x' : List Bool) → (x : Bool) → (xs : List Bool) → x' = x :: xs → x✝ = x :: xs → motive (x :: xs))
  (h_2 : (x' : List Bool) → x✝ = x' → motive x') (x : Bool) (xs : List Bool) (heq_1 : x✝ = x :: xs) :
  (match hx : x✝ with
    | x'@hx':(x :: xs) => h_1 x' x xs hx' hx
    | x' => h_2 x' hx) ≍
    h_1 (x :: xs) x xs ⋯ heq_1
-/
#guard_msgs(pass trace, all) in
#check myNamedPatternTest.match_1.congr_eq_1

set_option linter.unusedVariables false in
def testMe (n : Nat) : Bool :=
  match _ : n - 2 with
  | 0 => true
  | m => false

/--
info: testMe.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : x✝ = 0 → motive 0)
  (h_2 : (m : Nat) → x✝ = m → motive m) (m : Nat) (heq_1 : x✝ = m) :
  (m = 0 → False) →
    (match h : x✝ with
      | 0 => h_1 h
      | m => h_2 m h) ≍
      h_2 m heq_1
-/
#guard_msgs(pass trace, all) in
#check testMe.match_1.congr_eq_2

-- JFR: Code to check if all matchers with equations also have congruence equations
/-
open Lean Meta in
run_meta do
  -- if false do -- comment this line to run the test on all matchers in the environment
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
            let _ ← Lean.Meta.Match.Match.gendMatchCongrEqns k
          catch e =>
            logError m!"failed to generate equations for {k} in {.ofConstName k.getPrefix}\n{indentD e.toMessageData}"
-/
