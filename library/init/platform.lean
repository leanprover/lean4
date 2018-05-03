/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core

namespace system

structure platform_type :=
(nbits : nat)

-- TODO: mark as opaque
def platform : platform_type :=
{ nbits := 64 } -- TODO use `default nat` }

end system
