/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic

namespace System
namespace Platform

@[extern "lean_system_platform_nbits"]
constant getNumBits : Unit → Nat := default _

@[extern "lean_system_platform_windows"]
constant getIsWindows : Unit → Bool := default _

def numBits : Nat := getNumBits ()
def isWindows : Bool := getIsWindows ()

end Platform
end System
