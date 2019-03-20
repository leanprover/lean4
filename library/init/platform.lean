/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core

namespace System

-- TODO: mark as opaque, the VM provides platform specific implementation
def platform.nbits : Nat := 64

end System
