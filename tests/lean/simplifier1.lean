/- Basic rewriting with eq without congruence or conditionals -/
universe l
constant T : Type.{l}
constants (x y z : T) (f g h : T → T)
constants (Hfxgy : f x = g y) (Hgyhz : g y = h z)

namespace tst attribute Hfxgy [simp] end tst
#simplify eq tst 2 (f x)
namespace tst attribute Hgyhz [simp] end tst
#simplify eq tst 2 (f x)
