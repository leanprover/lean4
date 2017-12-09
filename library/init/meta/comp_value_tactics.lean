/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.data.option.basic

meta constant mk_nat_val_ne_proof : expr → expr → option expr
meta constant mk_nat_val_lt_proof : expr → expr → option expr
meta constant mk_nat_val_le_proof : expr → expr → option expr
meta constant mk_fin_val_ne_proof : expr → expr → option expr
meta constant mk_char_val_ne_proof : expr → expr → option expr
meta constant mk_string_val_ne_proof : expr → expr → option expr
meta constant mk_int_val_ne_proof : expr → expr → option expr

namespace tactic
open expr
meta def comp_val : tactic unit :=
do t ← target >>= instantiate_mvars,
   guard (is_app t),
   type ← infer_type t.app_arg,
   (do is_def_eq type (const `nat []),
       (do (a, b) ← is_ne t,
           pr     ← mk_nat_val_ne_proof a b,
           exact pr)
       <|>
       (do (a, b) ← is_lt t,
           pr     ← mk_nat_val_lt_proof a b,
           exact pr)
       <|>
       (do (a, b) ← is_gt t,
           pr     ← mk_nat_val_lt_proof b a,
           exact pr)
       <|>
       (do (a, b) ← is_le t,
           pr     ← mk_nat_val_le_proof a b,
           exact pr)
       <|>
       (do (a, b) ← is_ge t,
           pr     ← mk_nat_val_le_proof b a,
           exact pr))
   <|>
   (do is_def_eq type (const `char []),
       (a, b) ← is_ne t,
       pr     ← mk_char_val_ne_proof a b,
       exact pr)
   <|>
   (do is_def_eq type (const `string []),
       (a, b) ← is_ne t,
       pr     ← mk_string_val_ne_proof a b,
       exact pr)
   <|>
   (do is_def_eq type (const `int []),
       (a, b) ← is_ne t,
       pr     ← mk_int_val_ne_proof a b,
       exact pr)
   <|>
   (do type   ← whnf type,
       guard (is_napp_of type `fin 1),
       (a, b) ← is_ne t,
       pr     ← mk_fin_val_ne_proof a b,
       exact pr)
   <|>
   (do (a, b) ← is_eq t,
        unify a b, to_expr ``(eq.refl %%a) >>= exact)
end tactic

namespace tactic
namespace interactive
/-- Close goals of the form `n ≠ m` when `n` and `m` have type `nat`, `char`, `string`, `int` or `fin sz`,
    and they are literals. It also closes goals of the form `n < m`, `n > m`, `n ≤ m` and `n ≥ m` for `nat`.
    If the foal is of the form `n = m`, then it tries to close it using reflexivity. -/
meta def comp_val := tactic.comp_val
end interactive
end tactic
