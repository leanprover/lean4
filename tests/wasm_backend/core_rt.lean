module

import core_rt_lib

/-!
Pure multi-module program that needs only the language-core wasm runtime
(constructors, RC, cross-module calls) — no IO / tasks / libuv.
-/

@[export lean_wasm_core_rt]
def coreRt (x y : UInt32) : UInt32 :=
  let p := CorePair.mk x y
  let p := corePairScale p 2
  corePairSum p
