/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise
import Init.Data.SInt
import Std.Net

namespace Std
namespace Internal
namespace UV
namespace Signal

open Std.Net

/--
Creates a new promise that is resolved when the `signum` signal is received.
-/
@[extern "lean_uv_signal_wait"]
opaque waitFor (signum : Int) : IO (IO.Promise (Except IO.Error Unit))

end Signal
end UV
end Internal
end Std
