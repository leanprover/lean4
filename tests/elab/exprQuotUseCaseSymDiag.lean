import Lean

/-!
# The `/sym` engine in `sym =>` tactics, and `expr` quotation diagnostics

- `/sym` matching in `SymM`: numerals vs. `Sym` offsets (`Nat.succ ?n` and `?n + 2` decompose
  numeral literals) and maximally shared term building;
- a custom `sym =>` tactic (`even_sym`) dispatching on the goal with `/sym` patterns through the
  `MonadSym` instance of `GrindTacticM`;
- `#check_pattern`, `trace.Meta.Match.expr`, error hints, and the `exprQuot` linters.
-/

namespace ExprQuotSymDiag
open Lean Meta Elab Tactic
open Lean.Meta.Sym (SymM)

/-! ## `/sym` numerals and offsets -/

/-- Predecessor of a successor-like term: `n + 1`, `Nat.succ n` and literals `k + 1` alike. -/
def pred? (e : Expr) : SymM (Option Expr) := do
  match e with
  | `(expr/sym| Nat.succ ?n) => return some n
  | _ => return none

/-- info: [4, x, x + 1, none] -/
#guard_msgs in
run_meta withLocalDeclD `x (mkConst ``Nat) fun x => SymM.run do
  -- Terms built with `/sym` are maximally shared, ready for `Sym`-based automation.
  let xp1 ← `(expr/sym| ($x : Nat) + 1)
  let xp2 ← `(expr/sym| Nat.succ ($x + 1))
  let rs ← [mkNatLit 5, xp1, xp2, mkNatLit 0].mapM pred?
  logInfo m!"{rs.map (·.getD (mkConst `none))}"

/-! ## A `sym =>` tactic dispatching with `/sym` patterns -/

inductive Even : Nat → Prop
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

/-- `even_sym` proves `Even k` for numerals `k` by peeling offsets `?n + 2` off the goal. -/
syntax (name := evenSym) "even_sym" : grind

open Lean.Elab.Tactic.Grind in
/-- Loop of `even_sym`: one `apply` per matched `/sym` pattern. -/
partial def evenSymLoop : GrindTacticM Unit := do
  let goal ← getMainGoal
  match ← instantiateMVars (← goal.mvarId.getType) with
  | `(expr/sym| Even 0) => evalGrindTactic (← `(grind| apply Even.zero))
  | `(expr/sym| Even (?n + 2)) =>
    -- `/sym` sees `Even 6` as `Even (4 + 2)`; the capture is the numeral `4`.
    unless (← getNatValue? n).isSome do throwError "even_sym: symbolic argument {n}"
    evalGrindTactic (← `(grind| apply Even.add_two))
    evenSymLoop
  | tgt => throwError "even_sym: cannot prove{indentExpr tgt}"

open Lean.Elab.Tactic.Grind in
@[grind_tactic evenSym] def evalEvenSym : GrindTactic := fun _ => evenSymLoop

example : Even 6 := by
  sym => even_sym

/-- error: even_sym: cannot prove
  Even 1 -/
#guard_msgs in
example : Even 5 := by
  sym => even_sym

/-! ## Diagnostics -/

/--
info: pattern: ?x + ?y
relation: structural [-inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?x : Nat (first-order), ?y : Nat (first-order)
pins: none
wildcards: none
fixed instances: `instHAdd` : HAdd Nat Nat Nat (at `HAdd.hAdd` arg #3),
  `instAddNat` : Add Nat (at `instHAdd` arg #1)
polymorphic instances: none
universe params: none
closed proofs: none
indexing: eligible (DiscrTree keys: [HAdd.hAdd, Nat, Nat, Nat, instHAdd, Nat, instAddNat, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr| (?x : Nat) + ?y)

/-- Two indexed arms: the trace shows which candidates the discrimination tree selected. -/
def classify (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| (?a : Nat) * $a) => let _ := a; return 1
  | `(expr| Nat.succ ?n) => let _ := n; return 2
  | _ => return 0

/--
trace: [Meta.Match.expr] [indexed structural] trying candidates [0] of 2 for:
      2 * 3
[Meta.Match.expr] [structural] failed:
      ?a * ?a
    against:
      2 * 3
    first mismatch:
      2
    against:
      3
    (literal mismatch)
-/
#guard_msgs (whitespace := lax) in
run_meta withOptions (·.setBool `trace.Meta.Match.expr true) do
  discard <| classify (← `(expr| (2 : Nat) * (3 : Nat)))

/-- error: repeated pattern variable `?x`; use `$x` to pin -/
#guard_msgs in
def sameSummands? (e : Expr) : MetaM Bool := do
  let `(expr| ?x + ?x) := e | return false
  return true

/--
warning: pattern numeral `0` relies on defaulting to `Nat`;
add a type annotation such as `(0 : Nat)`

Note: This linter can be disabled with `set_option linter.exprQuot.numeralDefaulting false`
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.numeralDefaulting true in
def isAddZero (e : Expr) : MetaM Bool := do
  let `(expr| _ + 0) := e | return false
  return true

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def forgotExprKeyword (e : Expr) : Nat :=
  match e with
  | `(?x + 1) => 1
  | _ => 0

end ExprQuotSymDiag
