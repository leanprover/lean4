/-
Unit tests for `contextDependent` propagation in Sym.simp combinators.
-/
import Lean
open Lean Meta

private def e := mkConst ``True
private def rflProof := mkApp2 (mkConst ``Eq.refl [1]) (mkSort 0) e

-- mkRflResultCD
#eval do assert! !(Sym.Simp.mkRflResultCD false).isContextDependent
#eval do assert! (Sym.Simp.mkRflResultCD true).isContextDependent
-- isRfl checks done=false, ignores contextDependent
#eval do assert! (Sym.Simp.mkRflResultCD false).isRfl
#eval do assert! (Sym.Simp.mkRflResultCD true).isRfl
#eval do assert! !(Sym.Simp.mkRflResult (done := true)).isRfl

-- mkRflResult
#eval do assert! !(Sym.Simp.mkRflResult).isContextDependent
#eval do assert! (Sym.Simp.mkRflResult (contextDependent := true)).isContextDependent
#eval do assert! (Sym.Simp.mkRflResult (done := true) (contextDependent := true)).isContextDependent

-- Result.withContextDependent
#eval do assert! (Sym.Simp.Result.rfl).withContextDependent.isContextDependent
#eval do assert! (Sym.Simp.Result.step e rflProof).withContextDependent.isContextDependent

-- mkEqTransResult: cd₁=true, r₂ cd=false → combined cd=true
#eval show MetaM Unit from Sym.SymM.run do
  let r ← Sym.Simp.mkEqTransResult e e rflProof (.step e rflProof) (cd₁ := true)
  assert! r.isContextDependent

-- mkEqTransResult: cd₁=false, r₂ cd=true → combined cd=true
#eval show MetaM Unit from Sym.SymM.run do
  let r ← Sym.Simp.mkEqTransResult e e rflProof (.step e rflProof false true)
  assert! r.isContextDependent

-- mkEqTransResult: cd₁=false, r₂ cd=false → combined cd=false
#eval show MetaM Unit from Sym.SymM.run do
  let r ← Sym.Simp.mkEqTransResult e e rflProof (.step e rflProof)
  assert! !r.isContextDependent

-- mkEqTransResult: cd₁=true, r₂=rfl cd=false → combined cd=true
#eval show MetaM Unit from Sym.SymM.run do
  let r ← Sym.Simp.mkEqTransResult e e rflProof (.rfl) (cd₁ := true)
  assert! r.isContextDependent

-- andThen: f returns .rfl (cd=true), g returns .step (cd=false)
-- cd from f propagates: in another context f might succeed, changing the path.
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .rfl false true
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof
  let r ← Sym.Simp.SimpM.run' ((f.andThen g) e)
  assert! r.isContextDependent

-- andThen: f returns .rfl (cd=false), g returns .step (cd=true) → cd from g
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .rfl
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof false true
  let r ← Sym.Simp.SimpM.run' ((f.andThen g) e)
  assert! r.isContextDependent

-- andThen: f .rfl (cd=false), g .step (cd=false) → no cd
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .rfl
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof
  let r ← Sym.Simp.SimpM.run' ((f.andThen g) e)
  assert! !r.isContextDependent

-- andThen transitivity: f step (cd=true), g step (cd=false)
-- Exercises mkEqTransResult through andThen.
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .step e rflProof false true
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof
  let r ← Sym.Simp.SimpM.run' ((f.andThen g) e)
  assert! r.isContextDependent

-- andThen transitivity: f step (cd=false), g step (cd=true)
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .step e rflProof
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof false true
  let r ← Sym.Simp.SimpM.run' ((f.andThen g) e)
  assert! r.isContextDependent

-- orElse: f returns .rfl (cd=true), g returns .step (cd=false)
-- cd from f propagates: in another context f might succeed.
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .rfl false true
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof
  let r ← Sym.Simp.SimpM.run' ((f.orElse g) e)
  assert! r.isContextDependent

-- orElse: f returns .rfl (cd=false), g returns .step (cd=true) → cd from g
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .rfl
  let g : Sym.Simp.Simproc := fun _ => return .step e rflProof false true
  let r ← Sym.Simp.SimpM.run' ((f.orElse g) e)
  assert! r.isContextDependent

-- orElse: f returns .step → returned directly, g not called
#eval show MetaM Unit from Sym.SymM.run do
  let f : Sym.Simp.Simproc := fun _ => return .step e rflProof false true
  let g : Sym.Simp.Simproc := fun _ => unreachable!
  let r ← Sym.Simp.SimpM.run' ((f.orElse g) e)
  assert! r.isContextDependent
