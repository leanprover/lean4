import Lean

def ident := String deriving BEq, Repr, Hashable

inductive aexp : Type where
  | CONST (n : Int)               -- a constant, or
  | VAR (x : ident)               -- a variable, or
  | PLUS (a1 : aexp) (a2 : aexp)  -- a sum of two expressions, or
  | MINUS (a1 : aexp) (s2 : aexp) -- a difference of two expressions

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2

/-
  Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its free variables.

  Free variables are defined by this recursive predicate:
-/
@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2
  | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

theorem aeval_free (s1 s2 a) (h : ∀ x, free_in_aexp x a → s1 x = s2 x) :
    aeval s1 a = aeval s2 a := by
  fun_induction aeval s1 a with grind

/-
  1.3 Boolean expressions

  The IMP language has conditional statements (if/then/else) and loops.  They are controlled by expressions that evaluate to Boolean values.  Here is the abstract syntax of Boolean expressions.
-/

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1 : aexp) (a2 : aexp)     -- whether [a1=a]
  | LESSEQUAL (a1 : aexp) (a2 : aexp) -- whether [a1≤a]
  | NOT (b1 : bexp)                   -- Boolean negation
  | AND (b1 : bexp) (b2 : bexp)       -- Boolean conjunction

/-
  There are many useful derived forms.
-/
def NOTEQUAL (a1 a2 : aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2 : aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2 : aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2 : aexp) : bexp := GREATER a2 a1

@[grind] def OR (b1 b2 : bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))

/-
Just like arithmetic expressions evaluate to integers, Boolean expressions evaluate to Boolean values `true` or `false`.
-/
@[grind] def beval (s : store) (b : bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

/-
  We show the expected semantics for the `OR` derived form:
-/
theorem beval_OR : beval s (OR b1 b2) = beval s b1 ∨ beval s b2 := by grind

/-
  1.4 Commands

  To complete the definition of the IMP language, here is the abstract syntax of commands, also known as statements.
-/
inductive com : Type where
  | SKIP                                        -- do nothing
  | ASSIGN (x : ident) (a : aexp)               -- assignment: [v := a]
  | SEQ (c1 : com) (c2 : com)                   -- sequence: [c1; c2]
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com) -- conditional: [if b then c1 else c2]
  | WHILE (b : bexp) (c1 : com)                 -- loop: [while b do c1 done]

--  We can write `c1 ;; c2` instead of `.SEQ c1 c2`, it is easier on the eyes.
notation:10 l:10 " ;; " r:11 => com.SEQ l r


@[grind] def update (x : ident) (v : Int) (s : store) : store :=
  fun y => if x == y then v else s y

@[grind] def cexec_bounded (fuel : Nat) (s : store) (c : com) : Option store :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    match c with
    | .SKIP => .some s
    | .ASSIGN x a => .some (update x (aeval s a) s)
    | .SEQ c1 c2 =>
      match cexec_bounded fuel' s c1 with
      | .none => .none
      | .some s' => cexec_bounded fuel' s' c2
    | .IFTHENELSE b c1 c2 =>
      if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
    | .WHILE b c1 =>
      if beval s b then
        match cexec_bounded fuel' s c1 with
        | .none => .none
        | .some s' => cexec_bounded fuel' s' (.WHILE b c1)
      else
        .some s

open Lean

def mkSeq (e₁ e₂ : Expr) : Expr := mkApp2 (mkConst ``com.SEQ) e₁ e₂

def buildProblemInstance (n : Nat) : MetaM Expr := do match n with
  | .zero => return mkConst ``com.SKIP
  | .succ n =>
    let var_x := mkApp (mkConst ``aexp.VAR) (mkStrLit "x")
    let assign_to_x := mkApp2 (mkConst ``com.ASSIGN) (mkStrLit "x")
    let set_x_to_x_plus_two := assign_to_x <| mkApp2 (mkConst ``aexp.PLUS) var_x (mkApp (mkConst ``aexp.CONST) (mkIntLit 2))
    let set_x_to_x_minus_one := assign_to_x <| mkApp2 (mkConst ``aexp.MINUS) var_x (mkApp (mkConst ``aexp.CONST) (mkIntLit 1))
    let res := mkSeq (mkSeq set_x_to_x_plus_two set_x_to_x_minus_one) (← buildProblemInstance n)
    return res

def emptyStore : store := fun _ => 0

def createInstance (n : Nat) : MetaM Expr := do
  let res := mkApp3 (mkConst ``cexec_bounded) (mkNatLit (3 * n)) (mkConst ``emptyStore) (← buildProblemInstance n)
  let res ←  Meta.mkAppOptM ``Option.getD #[.none, res,  (mkConst ``emptyStore)]
  let res := mkApp res (mkStrLit "x")
  return res

def createDecideInstance (n : Nat) : MetaM Expr := do
  let lhs ← createInstance n
  let rhs := mkIntLit n
  let res := mkIntEq lhs rhs
  trace[Meta.Tactic] "res: {res}"
  return mkIntEq lhs rhs

def runSingleTest (n : Nat) : MetaM Unit := do
  let toFeed ← createInstance n
  let startTime ← IO.monoNanosNow
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry toFeed
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  match executed with
  | .rfl _ => IO.println s!"goal_{n}: {ms} ms"
  | .step e' proof _ =>
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel proof
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

def runSingleDecideTest (n : Nat) : MetaM Unit := do
  let toFeed ← createDecideInstance n
  let goalMVar ← Meta.mkFreshExprMVar toFeed
  let startTime ← IO.monoNanosNow
  let res := Lean.Elab.Tactic.evalDecideCore `native_decide {native := false}
  let res := Lean.Elab.Tactic.run goalMVar.mvarId! res
  let _ ← res.run'
  guard <| ← goalMVar.mvarId!.isAssigned
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel goalMVar
  let endTime ← IO.monoNanosNow
  let kernelMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"native_decide: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
def runCbvTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 150, 200, 250, 300, 350, 400, 450, 500, 600, 700, 800, 900, 1000] do
    runSingleTest n

def runDecideTests : MetaM Unit := do
  IO.println "=== Decide Tactic Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 150, 200, 250, 300, 350, 400, 450, 500, 600, 700, 800, 900, 1000] do
    runSingleDecideTest n


#eval runCbvTests
