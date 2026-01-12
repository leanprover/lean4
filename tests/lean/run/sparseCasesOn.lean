import Lean

/-- info: test._sparseCasesOn_1 -/
#guard_msgs in
run_meta
  Lean.withDeclNameForAuxNaming `test do
    let name ← Lean.Meta.mkSparseCasesOn ``Lean.Expr #[``Lean.Expr.fvar, ``Lean.Expr.sort]
    Lean.logInfo m!"{name}"

/--
info: test._sparseCasesOn_1.{u} {motive : Lean.Expr → Sort u} (t : Lean.Expr)
  (fvar : (fvarId : Lean.FVarId) → motive (Lean.Expr.fvar fvarId))
  (sort : (u : Lean.Level) → motive (Lean.Expr.sort u)) : (Nat.hasNotBit 10 t.ctorIdx → motive t) → motive t
-/
#guard_msgs in
#check test._sparseCasesOn_1

/--
info: theorem test._sparseCasesOn_1.else_eq.{u} : ∀ {motive : Lean.Expr → Sort u} (t : Lean.Expr)
  (fvar : (fvarId : Lean.FVarId) → motive (Lean.Expr.fvar fvarId)) (sort : (u : Lean.Level) → motive (Lean.Expr.sort u))
  («else» : Nat.hasNotBit 10 t.ctorIdx → motive t) (h : Nat.hasNotBit 10 t.ctorIdx),
  test._sparseCasesOn_1 t fvar sort «else» = «else» h
-/
#guard_msgs in
#print sig test._sparseCasesOn_1.else_eq

/-- error: mkSparseCasesOn: unexpected number of universe parameters in `Or.casesOn` -/
#guard_msgs in
run_meta
  Lean.withDeclNameForAuxNaming `test do
    let name ← Lean.Meta.mkSparseCasesOn ``Or #[``Or.inl]
    Lean.logInfo m!"{name}"


/- Check that the compiler is producin good code -/

set_option trace.Compiler.saveBase true

/--
trace: [Compiler.saveBase] size: 7
    def testDecl motive t fvar sort else.1 : motive lcAny :=
      cases t : motive lcAny
      | Lean.Expr.fvar fvarId =>
        let _x.2 := fvar fvarId;
        return _x.2
      | Lean.Expr.sort u =>
        let _x.3 := sort u;
        return _x.3
      | _ =>
        let _x.4 := else.1 _;
        return _x.4
-/
#guard_msgs in
def testDecl := @test._sparseCasesOn_1
