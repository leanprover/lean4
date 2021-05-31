/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Basic

namespace System
namespace Platform

@[extern "lean_system_platform_windows"] constant getIsWindows : Unit → Bool
@[extern "lean_system_platform_osx"] constant getIsOSX : Unit → Bool
@[extern "lean_system_platform_emscripten"] constant getIsEmscripten : Unit → Bool

def isWindows : Bool := getIsWindows ()
def isOSX : Bool := getIsOSX ()
def isEmscripten : Bool := getIsEmscripten ()

end Platform
end System
