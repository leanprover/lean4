import Lean

/-!
Tests for `expr` quotation diagnostics (`core_spec_v1.md` §7):
- `#check_pattern` across relations, `[items]`, higher-order binders, pins/self-pins, wildcards,
  unresolved implicits, fixed vs polymorphic instances, universe params, closed proofs, and
  `DiscrTree` indexing eligibility (without running term-builder template mode).
- `trace.Meta.Match.expr` across `.structural`, `.reducible`, `.defeq`, `.sym`, and indexed
  dispatch, reporting alternatives tried and the first mismatch subterm.
- Pattern & pin errors (repeated `?x`, out-of-scope `$x` `"did you mean ?x"`).
- `linter.exprQuot.numeralDefaulting` (positive and negative cases).
- Strictly scoped `linter.exprQuot.syntaxHole` (`Expr`-typed patterns/terms only; never `?_`,
  tactic quotations, or `Syntax`/`TSyntax` quotations).
-/

namespace ExprQuotDiagTest

open Lean Meta Elab Tactic
open Lean.Meta.Sym (SymM)

/-! ## 1. `#check_pattern` command (pattern path only, no term-builder) -/

section CheckPatternStructuralWildcard

/--
info: pattern: ?x + _
relation: structural [-inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?x : Nat (first-order)
pins: none
wildcards:
  var #1 : Nat [explicit `_`/`?_` @ `HAdd.hAdd` arg #5 (explicit); not captured]
fixed instances: `instHAdd` : HAdd Nat Nat Nat (at `HAdd.hAdd` arg #3),
  `instAddNat` : Add Nat (at `instHAdd` arg #1)
polymorphic instances: none
universe params: none
closed proofs: none
indexing: eligible (DiscrTree keys: [HAdd.hAdd, Nat, Nat, Nat, instHAdd, Nat, instAddNat, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr| (?x : Nat) + _)

end CheckPatternStructuralWildcard

section CheckPatternPlusInstPoly

/--
info: pattern: ?a + ?b
relation: structural [+inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?a : _ (first-order), ?b : _ (first-order)
pins: none
wildcards:
  var #0 : Type u_1 [unresolved implicit @ `HAdd.hAdd` arg #0 (implicit); not captured]
  var #1 : Type u_2 [unresolved implicit @ `HAdd.hAdd` arg #1 (implicit); not captured]
  var #2 : Type u_3 [unresolved implicit @ `HAdd.hAdd` arg #2 (implicit); not captured]
  var #3 : HAdd _ _ _ [unresolved implicit @ `HAdd.hAdd` arg #3 (inst); not captured]
fixed instances: none
polymorphic instances: `_` (at `HAdd.hAdd` arg #3)
universe params: u_1, u_2, u_3
closed proofs: none
indexing: eligible (DiscrTree keys: [HAdd.hAdd, *, *, *, *, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr +inst| ?a + ?b)

end CheckPatternPlusInstPoly

section CheckPatternHigherOrderBinder

/--
info: pattern: fun x => ?P x
relation: structural [-inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?P : (x : Nat) → _ x (higher-order arity=1)
pins: none
wildcards:
  var #0 : Nat → Sort u_1 [explicit `_` / implicit; not captured]
fixed instances: none
polymorphic instances: none
universe params: u_1
closed proofs: none
indexing: eligible (DiscrTree keys: [◾])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr| fun x : Nat => ?P x)

end CheckPatternHigherOrderBinder

section CheckPatternNonlinearSelfPin

/--
info: pattern: ?x + ?x
relation: structural [-inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?x : _ (first-order, nonlinear self-pins=1)
pins: none
wildcards:
  var #0 : Type u_1 [unresolved implicit @ `HAdd.hAdd` arg #0 (implicit),
    `HAdd.hAdd` arg #1 (implicit); captured (repeated)]
  var #1 : Type u_2 [unresolved implicit @ `HAdd.hAdd` arg #2 (implicit); not captured]
  var #2 : HAdd _ _ _ [unresolved implicit @ `HAdd.hAdd` arg #3 (inst); not captured]
fixed instances: none
polymorphic instances: `_` (at `HAdd.hAdd` arg #3)
universe params: u_1, u_2
closed proofs: none
indexing: eligible (DiscrTree keys: [HAdd.hAdd, *, *, *, *, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr| ?x + $x)

end CheckPatternNonlinearSelfPin

section CheckPatternReducibleItems

def customUnfold (n : Nat) : Nat := n + 1
opaque carryProof {P : Prop} (h : P) (x : Nat) : Nat

/--
info: pattern: carryProof trivial ?x
relation: reducible [+inst, +beta, +zeta, +proj, +eta] (items: +ExprQuotDiagTest.customUnfold)
binders: ?x : Nat (first-order)
pins: none
wildcards: none
fixed instances: none
polymorphic instances: none
universe params: none
closed proofs: `trivial` : `True`
indexing: eligible (DiscrTree keys: [ExprQuotDiagTest.carryProof, True, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr/reducible [+customUnfold]| carryProof trivial ?x)

end CheckPatternReducibleItems

section CheckPatternIneligibleLookThrough

/--
info: pattern: id ?x
relation: structural [-inst, +beta, -zeta, -proj, -eta] (items: none)
binders: ?x : _ (first-order)
pins: none
wildcards:
  var #0 : Sort u_1 [unresolved implicit @ `id` arg #0 (implicit); not captured]
fixed instances: none
polymorphic instances: none
universe params: u_1
closed proofs: none
indexing: ineligible (enabled look-through flag prevents static structural indexing)
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr +beta| _root_.id ?x)

end CheckPatternIneligibleLookThrough

section CheckPatternSymRelation

/--
info: pattern: Nat.succ ?n
relation: sym [+inst, +beta, +zeta, +proj, +eta] (items: none)
binders: ?n : Nat (first-order)
pins: none
wildcards: none
fixed instances: none
polymorphic instances: none
universe params: none
closed proofs: none
indexing: eligible (DiscrTree keys: [*])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr/sym| Nat.succ ?n)

end CheckPatternSymRelation

section CheckWithSectionVar
variable (pinVal : Expr)

/--
info: pattern: «$pinVal» + ?y
relation: structural [-inst, -beta, -zeta, -proj, -eta] (items: none)
binders: ?y : Nat (first-order)
pins: $pinVal : Nat (var #0)
wildcards: none
fixed instances: `instHAdd` : HAdd Nat Nat Nat (at `HAdd.hAdd` arg #3),
  `instAddNat` : Add Nat (at `instHAdd` arg #1)
polymorphic instances: none
universe params: none
closed proofs: none
indexing: eligible (DiscrTree keys: [HAdd.hAdd, Nat, Nat, Nat, instHAdd, Nat, instAddNat, *, *])
-/
#guard_msgs (whitespace := lax) in
#check_pattern `(expr| $pinVal + (?y : Nat))

end CheckWithSectionVar

section CheckPatternInvalidArgError

/-- error: expected an `` `(expr[rel]| p) `` pattern quotation -/
#guard_msgs in
#check_pattern (1 + 2)

end CheckPatternInvalidArgError

/-! ## 2. `trace.Meta.Match.expr` reporting alternatives and first mismatch subterm -/

section TraceStructuralMatch

opaque customF : Nat → Nat

private def traceStructMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| (?x : Nat) + (?y : Nat)) => let _ := (x, y); return 1
  | `(expr| (?a : Nat) * $a)         => let _ := a; return 2
  | `(expr| customF ?n)              => let _ := n; return 3
  | _                                => return 0

/--
info: res=3
---
trace: [Meta.Match.expr] [indexed structural] trying candidates [2] of 3 for:
      customF (1 + 2)
[Meta.Match.expr] [structural] matched:
      customF ?n
    against:
      customF (1 + 2)
-/
#guard_msgs (whitespace := lax) in
run_meta withOptions (fun o => o.setBool `trace.Meta.Match.expr true) do
  let e1 ← `(expr| customF ((1 : Nat) + (2 : Nat)))
  let r1 ← traceStructMatch e1
  logInfo m!"res={r1}"

/--
info: res=0
---
trace: [Meta.Match.expr] [indexed structural] trying candidates [1] of 3 for:
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
run_meta withOptions (fun o => o.setBool `trace.Meta.Match.expr true) do
  let e2 ← `(expr| (2 : Nat) * (3 : Nat))
  let r2 ← traceStructMatch e2
  logInfo m!"res={r2}"

end TraceStructuralMatch

section TraceDefeqMatch

private def traceNonIndexedMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/defeq| (1 : Nat) + ?x) => let _ := x; return 1
  | `(expr/defeq| ?x + (2 : Nat)) => let _ := x; return 2
  | _                             => return 0

/--
info: defeq=2
---
trace: [Meta.Match.expr] [defeq] failed:
      1 + ?x
    against:
      3 + 2
    first mismatch:
      1
    against:
      3
    (defeq mismatch)
[Meta.Match.expr] [defeq] matched:
      ?x + 2
    against:
      3 + 2
-/
#guard_msgs (whitespace := lax) in
run_meta withOptions (fun o => o.setBool `trace.Meta.Match.expr true) do
  let e ← `(expr| (3 : Nat) + (2 : Nat))
  let r ← traceNonIndexedMatch e
  logInfo m!"defeq={r}"

end TraceDefeqMatch

section TraceSymMatch

private def traceSymMatch (e : Expr) : SymM Nat :=
  match e with
  | `(expr/sym| (?a : Nat) + (5 : Nat)) => let _ := a; return 1
  | `(expr/sym| (?a : Nat) + (3 : Nat)) => let _ := a; return 2
  | _                                   => return 0

/--
info: sym=2
---
trace: [Meta.Match.expr] [indexed sym] trying candidates [0, 1] of 2 for:
      4 + 3
[Meta.Match.expr] [sym] failed:
      ?a + 5
    against:
      4 + 3
    first mismatch:
      5
    against:
      3
    (sym mismatch)
[Meta.Match.expr] [sym] matched:
      ?a + 3
    against:
      4 + 3
-/
#guard_msgs (whitespace := lax) in
run_meta withOptions (fun o => o.setBool `trace.Meta.Match.expr true) do
  SymM.run do
    let e ← `(expr/sym| (4 : Nat) + (3 : Nat))
    let r ← traceSymMatch e
    logInfo m!"sym={r}"

end TraceSymMatch

/-! ## 3. Repeated `?x` and out-of-scope `$x` errors -/

section DiagRepeatedVar

/-- error: repeated pattern variable `?x`; use `$x` to pin -/
#guard_msgs in
def diagRepeatedVar (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| ?x + ?x) => let _ := x; return true
  | _ => return false

end DiagRepeatedVar

section DiagOutOfScopePinPat

/-- error: unknown identifier `missingVar` in `$`-pin (did you mean `?missingVar`?) -/
#guard_msgs in
def diagOutOfScopePinPat (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| $missingVar + (?y : Nat)) => let _ := y; return true
  | _ => return false

end DiagOutOfScopePinPat

section DiagOutOfScopePinTerm

/-- error: unknown identifier `missingTermVar` in `$`-pin (did you mean `?missingTermVar`?) -/
#guard_msgs in
def diagOutOfScopePinTerm : MetaM Expr :=
  `(expr| $missingTermVar + (1 : Nat))

end DiagOutOfScopePinTerm

/-! ## 4. `linter.exprQuot.numeralDefaulting` -/

section LintNumeralDefaultRight

/--
warning: pattern numeral `1` relies on defaulting to `Nat`;
add a type annotation such as `(1 : Nat)`

Note: This linter can be disabled with `set_option linter.exprQuot.numeralDefaulting false`
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.numeralDefaulting true in
def lintNumeralDefaultRight (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| ?x + 1) => let _ := x; return true
  | _ => return false

end LintNumeralDefaultRight

section LintNumeralDefaultLeft

/--
warning: pattern numeral `1` relies on defaulting to `Nat`;
add a type annotation such as `(1 : Nat)`

Note: This linter can be disabled with `set_option linter.exprQuot.numeralDefaulting false`
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.numeralDefaulting true in
def lintNumeralDefaultLeft (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| 1 + ?x) => let _ := x; return true
  | _ => return false

end LintNumeralDefaultLeft

section LintNumeralDefaultBare

/--
warning: pattern numeral `1` relies on defaulting to `Nat`;
add a type annotation such as `(1 : Nat)`

Note: This linter can be disabled with `set_option linter.exprQuot.numeralDefaulting false`
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.numeralDefaulting true in
def lintNumeralDefaultBare (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| 1) => return true
  | _ => return false

end LintNumeralDefaultBare

section NoLintNumeralAnnotated

-- Negative cases: annotated / `Nat`-typed patterns must NOT lint!
set_option linter.exprQuot.numeralDefaulting true in
#guard_msgs in
def noLintNumeralAnnotated (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| (?x : Nat) + 1) => let _ := x; return 1
  | `(expr| (1 : Nat) + ?x) => let _ := x; return 2
  | `(expr| Nat.succ 1)     => return 3
  | `(expr| (1 : Int) + ?x) => let _ := x; return 4
  | _                       => return 0

end NoLintNumeralAnnotated

/-! ## 5. Strictly scoped `linter.exprQuot.syntaxHole` -/

section LintSyntaxHoleMatchExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleMatchExpr (e : Expr) : Nat :=
  match e with
  | `(?x + 1) => 1
  | _ => 0

end LintSyntaxHoleMatchExpr

section LintSyntaxHoleIfLetExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleIfLetExpr (e : Expr) : Nat :=
  if let `(?x + 1) := e then 1 else 0

end LintSyntaxHoleIfLetExpr

section LintSyntaxHoleDoMatchExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleDoMatchExpr (e : Expr) : MetaM Nat := do
  match e with
  | `(?x + 1) => return 1
  | _ => return 0

end LintSyntaxHoleDoMatchExpr

section LintSyntaxHoleDoLetElseExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleDoLetElseExpr (e : Expr) : MetaM Nat := do
  let `(?x + 1) := e | return 0
  return 1

end LintSyntaxHoleDoLetElseExpr

section LintSyntaxHoleFunPipeExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
---
error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) ``
-/
#guard_msgs (whitespace := lax) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleFunPipeExpr : Expr → Nat
  | `(?x) => 1
  | _ => 0

end LintSyntaxHoleFunPipeExpr

section LintSyntaxHoleTermExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
-/
#guard_msgs (whitespace := lax, drop error, check warning) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleTermExpr : Expr :=
  `(?x + 1)

end LintSyntaxHoleTermExpr

section LintSyntaxHoleMonadExpr

/--
warning: named pattern variable `?x` inside ordinary syntax quotation in an `Expr` context;
did you mean `` `(expr| ...) ``?

Note: This linter can be disabled with `set_option linter.exprQuot.syntaxHole false`
-/
#guard_msgs (whitespace := lax, drop error, check warning) in
set_option linter.exprQuot.syntaxHole true in
def lintSyntaxHoleMonadExpr : MetaM Expr :=
  `(?x + 1)

end LintSyntaxHoleMonadExpr

-- Negative cases: `?_`, tactic quotations, and `Syntax`/`TSyntax` must NEVER lint!

section NoLintAnonymousHole

set_option linter.exprQuot.syntaxHole true in
#guard_msgs in
def noLintAnonymousHole : TacticM (TSyntax `tactic) :=
  `(tactic| refine ?_)

end NoLintAnonymousHole

section NoLintSyntaxQuot

set_option linter.exprQuot.syntaxHole true in
#guard_msgs in
def noLintSyntaxQuot : MetaM (TSyntax `term) :=
  `(term| ?x)

end NoLintSyntaxQuot

section NoLintMatchSyntax

set_option linter.exprQuot.syntaxHole true in
#guard_msgs in
def noLintMatchSyntax (stx : Syntax) : Nat :=
  match stx with
  | `(?_ + 1) => 1
  | _ => 0

end NoLintMatchSyntax

section NoLintMatchSyntaxNamed

set_option linter.exprQuot.syntaxHole true in
#guard_msgs in
def noLintMatchSyntaxNamed (stx : TSyntax `term) : Nat :=
  match stx with
  | `(?x + 1) => 1
  | _ => 0

end NoLintMatchSyntaxNamed

section NoLintMatchExprAnonHole

set_option linter.exprQuot.syntaxHole true in
/-- error: syntax quotation pattern on an `Expr` discriminant; use `` `(expr| ...) `` -/
#guard_msgs in
def noLintMatchExprAnonHole (e : Expr) : Nat :=
  match e with
  | `(?_) => 1
  | _ => 0

end NoLintMatchExprAnonHole

section SyntaxMatchDiscrInfoPreserved

-- Normal `match (stx : Syntax)` must not elaborate discriminants during `match_syntax.expand`
-- and `elabMatchSyntax` must not add any extra discriminant elaboration or hover InfoTree entry.
private def discrMarker (s : Syntax) : Syntax := s

private def countDiscrMarkerInfos (trees : PersistentArray InfoTree) : Nat :=
  trees.foldl (init := (0 : Nat)) fun acc tree =>
    tree.foldInfo (init := acc) fun _ info n =>
      match info with
      | .ofTermInfo ti =>
        if ti.expr.isAppOfArity ``discrMarker 1 && !ti.isBinder then n + 1 else n
      | _ => n

#guard_msgs in
#eval show TermElabM Unit from do
  let stx ← `(fun (s : Syntax) => match discrMarker s with | `(?_ + 1) => (1 : Nat) | _ => 0)
  let savedInfo ← getInfoState
  try
    modifyInfoState fun s => { s with enabled := true, trees := {} }
    let expanded ← match stx with
      | `(fun ($s:ident : $ty) => $m) =>
        let expandedMatch : Term := ⟨← Term.Quotation.match_syntax.expand m⟩
        `(fun ($s:ident : $ty) => $expandedMatch)
      | _ => throwError "unexpected test syntax"
    let expandCount := countDiscrMarkerInfos (← getInfoTrees)
    unless expandCount == 0 do
      throwError "match_syntax.expand must not elaborate discriminants, got {expandCount}"
    modifyInfoState fun s => { s with enabled := true, trees := {} }
    discard <| Term.withoutModifyingElabMetaStateWithInfo <| Term.elabTerm expanded none
    let baselineCount := countDiscrMarkerInfos (← getInfoTrees)
    modifyInfoState fun s => { s with enabled := true, trees := {} }
    discard <| Term.withoutModifyingElabMetaStateWithInfo <| Term.elabTerm stx none
    let elabCount := countDiscrMarkerInfos (← getInfoTrees)
    unless elabCount == baselineCount do
      throwError "elabMatchSyntax duplicated discriminant elaboration: \
        expected {baselineCount}, got {elabCount}"
  finally
    setInfoState savedInfo

end SyntaxMatchDiscrInfoPreserved

section SyntaxMatchRhsErrorPreserved

/-- error: Unknown identifier `missingSyntaxMatchRhsId` -/
#guard_msgs in
def syntaxMatchRhsErrorPreserved (s : Syntax) : Nat :=
  match s with
  | `(?_ + 1) => missingSyntaxMatchRhsId
  | _ => 0

end SyntaxMatchRhsErrorPreserved

end ExprQuotDiagTest
