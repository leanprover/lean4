import Lean

/-!
The kernel must not reduce a projection whose structure name disagrees with the constructor it is
applied to.

`reduce_proj_core` used to select the field by index alone, so `.proj A 0 (B.mk 7)` reduced to `7`
even though `A` and `B` are unrelated. `infer_proj` rejects such a projection, so it can only reach
reduction from a declaration that was never checked; `debug.skipKernelTC` simulates that here.

Each check is a pair differing only in the projection's structure name, which isolates the
structure-name comparison from everything else in `reduce_proj_core`.
-/

open Lean

structure A where
  a : Nat

structure B where
  b : Nat

private def kwhnf (e : Expr) : CoreM Expr := do
  ofExceptKernelException (Kernel.whnf (← getEnv) {} e)

/-! Planted declarations: the projection reaches reduction by delta-unfolding a definition value,
which is the one path that is never re-inferred. -/

private def plant (n : Name) (sname : Name) : CoreM Unit :=
  addDecl <| .defnDecl {
    name := n, levelParams := [], type := mkConst ``Nat
    value := mkProj sname 0 (mkApp (mkConst ``B.mk) (mkRawNatLit 7))
    hints := .abbrev, safety := .safe }

set_option debug.skipKernelTC true in
#eval do plant `viaB ``B; plant `viaA ``A

/-- info: viaB ==> 7 -/
#guard_msgs in
#eval do IO.println s!"viaB ==> {← kwhnf (mkConst `viaB)}"

/-- info: viaA ==> (B.mk 7).1 -/
#guard_msgs in
#eval do IO.println s!"viaA ==> {← kwhnf (mkConst `viaA)}"

/-! String literals reach the same code path through `string_lit_to_constructor`, and are covered by
the same comparison: the constructor it produces belongs to `String`. -/

private def stuck (sname : Name) : CoreM Unit := do
  IO.println s!"{sname} on a string literal stuck? {(← kwhnf (mkProj sname 0 (mkStrLit "ab"))).isProj}"

/-- info: String on a string literal stuck? false -/
#guard_msgs in
#eval stuck ``String

/-- info: A on a string literal stuck? true -/
#guard_msgs in
#eval stuck ``A
