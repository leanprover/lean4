open tactic

-------------
namespace simp_lemmas

constants (A : Type.{1}) (x y z : A) (Hxy : x = y) (Hxz : x = z)
attribute Hxy [simp]
attribute Hxz [simp]

example : x = z := by simp

end simp_lemmas

-------------
namespace simp_lemmas_args

constants (A : Type.{1}) (x y z : A) (Hxy : x = y) (Hxz : x = z)
attribute Hxy [simp]

example : x = z :=
by do H ← mk_const `simp_lemmas_args.Hxz,
      simp_using [H]

end simp_lemmas_args

-------------
namespace simp_args

constants (A : Type.{1}) (x y z : A) (Hxy : x = y) (Hxz : x = z)

example : x = z :=
by do Hy ← mk_const `simp_args.Hxy,
      Hz ← mk_const `simp_args.Hxz,
      -- CONFIRM(leo): latter arguments should get priority?
      simp_using [Hy, Hz]

end simp_args

-------------
namespace simp_extensions

constants (A : Type.{1}) (x y z : A) (Hxy : x = y) (Hxz : x = z)

meta definition simp_x_to_y : tactic unit := mk_eq_simp_ext $
  λ e, do res ← mk_const `simp_extensions.y,
          pf ← mk_const `simp_extensions.Hxy,
          return (res, pf)

meta definition simp_x_to_z : tactic unit := mk_eq_simp_ext $
  λ e, do res ← mk_const `simp_extensions.z,
          pf ← mk_const `simp_extensions.Hxz,
          return (res, pf)

register_simp_ext x simp_x_to_y
register_simp_ext x simp_x_to_z

example : x = z := by simp

end simp_extensions

---------------
