/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.declaration

export lean (constant_info reducibility_hints)

namespace lean
namespace constant_info

/-- Instantiate a universe polymorphic declaration type with the given universes. -/
meta constant instantiate_type_univ_params : constant_info → list level → option expr

/-- Instantiate a universe polymorphic declaration value with the given universes. -/
meta constant instantiate_value_univ_params : constant_info → list level → option expr

end constant_info
end lean
