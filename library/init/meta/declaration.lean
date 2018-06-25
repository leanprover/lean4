/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.declaration

export lean (declaration reducibility_hints)

namespace lean
namespace declaration

/-- Instantiate a universe polymorphic declaration type with the given universes. -/
meta constant instantiate_type_univ_params : declaration → list level → option expr

/-- Instantiate a universe polymorphic declaration value with the given universes. -/
meta constant instantiate_value_univ_params : declaration → list level → option expr

end declaration
end lean
