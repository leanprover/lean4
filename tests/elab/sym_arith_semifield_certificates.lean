module

/-! Fast rational certificates for semifields, including carriers without additive cancellation. -/

open Lean.Grind

register_sym_simp semifieldCertSimp where
  pre := arith >> control >> arrow_telescope
  post := ground

set_option maxHeartbeats 1000

example {F : Type u} [Semifield F] [IsCharP F 0] (a b : F) :
    (a / 2 + b / 3)^32 * 6^32 = (3*a + 2*b)^32 := by
  sym => simp semifieldCertSimp

example {F : Type u} [Semifield F] [IsCharP F 0] (a b c : F) :
    (a / 2 + b / 3)^16 * 6^16 + c = (3*a + 2*b)^16 + c := by
  sym => simp semifieldCertSimp

example {F : Type u} [Semifield F] [IsCharP F 0] (f : F → F) (a b : F) :
    f ((a / 2 + b / 3)^32 * 6^32) = f ((3*a + 2*b)^32) := by
  sym => simp semifieldCertSimp

-- Many variables exceed the size bound of the nonlinear Kronecker point.
example {F : Type u} [Semifield F] [IsCharP F 0]
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : F) :
    (x0/2 + x1/2 + x2/2 + x3/2 + x4/2 + x5/2 +
      x6/2 + x7/2 + x8/2 + x9/2 + x10/2 + x11/2 +
      x12/2 + x13/2 + x14/2 + x15/2 + x16/2 + x17/2 +
      x18/2 + x19/2 + x20/2 + x21/2 + x22/2 + x23/2) +
    (x0/2 + x1/2 + x2/2 + x3/2 + x4/2 + x5/2 +
      x6/2 + x7/2 + x8/2 + x9/2 + x10/2 + x11/2 +
      x12/2 + x13/2 + x14/2 + x15/2 + x16/2 + x17/2 +
      x18/2 + x19/2 + x20/2 + x21/2 + x22/2 + x23/2) =
      x0 + x1 + x2 + x3 + x4 + x5 +
      x6 + x7 + x8 + x9 + x10 + x11 +
      x12 + x13 + x14 + x15 + x16 + x17 +
      x18 + x19 + x20 + x21 + x22 + x23 := by
  sym => simp semifieldCertSimp

-- With additive cancellation, the linear Kronecker point handles the same variables.
example {F : Type u} [Semifield F] [IsCharP F 0] [AddRightCancel F]
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : F) :
    (x0/2 + x1/2 + x2/2 + x3/2 + x4/2 + x5/2 +
      x6/2 + x7/2 + x8/2 + x9/2 + x10/2 + x11/2 +
      x12/2 + x13/2 + x14/2 + x15/2 + x16/2 + x17/2 +
      x18/2 + x19/2 + x20/2 + x21/2 + x22/2 + x23/2) +
    (x0/2 + x1/2 + x2/2 + x3/2 + x4/2 + x5/2 +
      x6/2 + x7/2 + x8/2 + x9/2 + x10/2 + x11/2 +
      x12/2 + x13/2 + x14/2 + x15/2 + x16/2 + x17/2 +
      x18/2 + x19/2 + x20/2 + x21/2 + x22/2 + x23/2) =
      x0 + x1 + x2 + x3 + x4 + x5 +
      x6 + x7 + x8 + x9 + x10 + x11 +
      x12 + x13 + x14 + x15 + x16 + x17 +
      x18 + x19 + x20 + x21 + x22 + x23 := by
  sym => simp semifieldCertSimp

open Lean.Grind.CommRing in
example {F : Type u} [Semifield F] [IsCharP F 0] (ctx : Context F)
    (h : InvVars.ok ctx [(1, 2)]) :
    (Expr.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))).denoteS ctx =
      (Expr.var 0).denoteS ctx :=
  Expr.eq_of_toPolyQS_eq ctx false [(1, 2)] h _ _ (by rfl)

open Lean.Grind.CommRing in
example {F : Type u} [Semifield F] [IsCharP F 0] (ctx : Context F)
    (h : InvVars.ok ctx [(1, 2)]) :
    (Expr.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))).denoteS ctx =
      (Expr.var 0).denoteS ctx :=
  Expr.eq_of_toPolyQS_eq ctx true [(1, 2)] h _ _ (by rfl)
