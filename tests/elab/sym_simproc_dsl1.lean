import Lean

open Lean Meta Sym.Simp Elab

/-! Tests for `sym_simproc` and `sym_discharger` DSL elaboration -/

theorem test_zero_add : 0 + n = n := Nat.zero_add n
theorem test_add_zero : n + 0 = n := Nat.add_zero n

/-- Run a `GrindTacticM` computation in a minimal test context. -/
def withTestGrindTacticM (k : Tactic.Grind.GrindTacticM α) : MetaM α := do
  let params ← Grind.mkDefaultParams {}
  let mvarId := (← mkFreshExprMVar (mkConst ``True)).mvarId!
  Grind.GrindM.run (params := params) do
    let methods ← Grind.getMethods
    let grindCtx ← readThe Meta.Grind.Context
    let symCtx ← readThe Sym.Context
    let grindState ← get
    let symState ← getThe Sym.State
    let ctx : Tactic.Grind.Context := {
      recover := false, elaborator := `test,
      ctx := grindCtx, sctx := symCtx, methods, params
    }
    let state : Tactic.Grind.State := { grindState, symState, goals := [] }
    Term.TermElabM.run' do
      let (a, _) ← Tactic.Grind.GrindTacticM.run k ctx state
      return a

/-- Elaborate a `sym_simproc` syntax to a `Simproc` in a test context. -/
def testElabSimproc (stx : TSyntax `sym_simproc) : MetaM Simproc :=
  withTestGrindTacticM (Tactic.Grind.elabSymSimproc stx)

/-- Elaborate a `sym_discharger` syntax to a `Discharger` in a test context. -/
def testElabDischarger (stx : TSyntax `sym_discharger) : MetaM Discharger :=
  withTestGrindTacticM (Tactic.Grind.elabSymDischarger stx)

/-- Run a simproc on a maximally-shared term. -/
def runSimproc (p : Simproc) (e : Expr) : MetaM Expr := Sym.SymM.run do
  let e ← Grind.shareCommon e
  match ← SimpM.run' (p e) with
  | .rfl _ _ => return e
  | .step e' _ _ _ => return e'

-- Test: `ground` elaborates and evaluates concrete terms
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| ground))
  let e := mkNatAdd (mkNatLit 3) (mkNatLit 4)
  let r ← runSimproc p e
  guard (r != e)

-- Test: `self` elaborates
#eval show MetaM Unit from do
  let _ ← testElabSimproc (← `(sym_simproc| self))

-- Test: `none` elaborates and is identity
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| none))
  let e := mkNatAdd (mkNatLit 3) (mkNatLit 4)
  let r ← runSimproc p e
  guard (r == e)

-- Test: `rewrite [thm]` elaborates and rewrites
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| rewrite [test_zero_add]))
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let e := mkNatAdd (mkNatLit 0) x
    let r ← runSimproc p e
    guard (r == x)

-- Test: `>>` combinator elaborates and chains
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| rewrite [test_zero_add] >> rewrite [test_add_zero]))
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let inner := mkNatAdd x (mkNatLit 0)
    let e := mkNatAdd (mkNatLit 0) inner
    let r ← runSimproc p e
    guard (r == x)

-- Test: `<|>` combinator elaborates and falls through
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| rewrite [test_zero_add] <|> rewrite [test_add_zero]))
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let e := mkNatAdd x (mkNatLit 0)
    let r ← runSimproc p e
    guard (r == x)

-- Test: `ground >> rewrite [thm]` elaborates
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| ground >> rewrite [test_zero_add]))
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let e := mkNatAdd (mkNatLit 0) x
    let r ← runSimproc p e
    guard (r == x)

-- Test: parenthesized simproc elaborates
#eval show MetaM Unit from do
  let p ← testElabSimproc (← `(sym_simproc| (ground >> rewrite [test_zero_add])))
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let e := mkNatAdd (mkNatLit 0) x
    let r ← runSimproc p e
    guard (r == x)

-- Test: `self` discharger elaborates
#eval show MetaM Unit from do
  let _ ← testElabDischarger (← `(sym_discharger| self))

-- Test: `none` discharger elaborates
#eval show MetaM Unit from do
  let _ ← testElabDischarger (← `(sym_discharger| none))

-- Test: `rewrite [thm] with self` elaborates
#eval show MetaM Unit from do
  let _ ← testElabSimproc (← `(sym_simproc| rewrite [test_zero_add] with self))

-- Test: `rewrite [thm] with none` elaborates
#eval show MetaM Unit from do
  let _ ← testElabSimproc (← `(sym_simproc| rewrite [test_zero_add] with none))
