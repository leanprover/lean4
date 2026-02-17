module

import CbvAttr.PubliclyVisibleTheorem
import CbvAttr.PublicFunctionLocalTheorem
import CbvAttr.PublicFunction
import CbvAttr.PublicFunctionPrivateTheorem
import CbvAttr.InvertedTheorem
import CbvAttr.InvertedLocalTheorem

set_option cbv.warning false

/- Function does not have an exposed body, but has a public theorem for unrolling it-/
example : f1 1 = 2 := by conv => lhs; cbv

/- Function has an exposed body, public theorem for unrolling it, but the attribute is local -/

/--
error: unsolved goals
⊢ f2 1 = 2
-/
#guard_msgs in
example : f2 1 = 2 := by conv => lhs; cbv

/- Function is public, but its body is not exposed -/

/--
error: unsolved goals
⊢ f3 1 = 2
-/
#guard_msgs in
example : f3 1 = 2 := by conv => lhs; cbv

/- Public function, that has an exposed body -/
example : f4 1 = 2 := by conv => lhs; cbv

/- Public function, private theorem-/

/--
error: unsolved goals
⊢ f5 1 = 2
-/
#guard_msgs in
example : f5 1 = 2 := by conv => lhs; cbv

/- Inverted public theorem: `x + 1 = f6 x` with ← becomes `f6 x = x + 1` -/
example : f6 1 = 2 := by conv => lhs; cbv

/- Inverted local theorem should not be visible across modules -/

/--
error: unsolved goals
⊢ f7 1 = 2
-/
#guard_msgs in
example : f7 1 = 2 := by conv => lhs; cbv
