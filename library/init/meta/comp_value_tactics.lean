/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

meta constant mk_nat_val_ne_proof : expr → expr → option expr
meta constant mk_nat_val_lt_proof : expr → expr → option expr
meta constant mk_nat_val_le_proof : expr → expr → option expr

namespace tactic
open expr
meta def comp_val : tactic unit :=
do t ← target,
   guard (is_app t),
   type ← infer_type t^.app_arg,
   guard (type = const `nat []),
   (do (a, b) ← returnopt (is_ne t),
       pr     ← returnopt (mk_nat_val_ne_proof a b),
       exact pr)
   <|>
   (do (a, b) ← returnopt (is_lt t),
       pr     ← returnopt (mk_nat_val_lt_proof a b),
       exact pr)
   <|>
   (do (a, b) ← returnopt (is_gt t),
       pr     ← returnopt (mk_nat_val_lt_proof b a),
       exact pr)
   <|>
   (do (a, b) ← returnopt (is_le t),
       pr     ← returnopt (mk_nat_val_le_proof a b),
       exact pr)
   <|>
   (do (a, b) ← returnopt (is_ge t),
       pr     ← returnopt (mk_nat_val_le_proof b a),
       exact pr)
   <|>
   (do (a, b) ← returnopt (is_eq t),
       unify a b, to_expr `(eq.refl %%a) >>= exact)
end tactic
