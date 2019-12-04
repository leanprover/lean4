/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Lean.Meta.SynthInstance

namespace Lean
namespace Meta

def mkEq (a b : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   pure $ mkAppB (mkApp (mkConst `Eq [u]) aType) a b

end Meta
end Lean
