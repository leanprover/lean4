/- 
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Factory
-/
import Lake
open Lake DSL

package EmitZig

lean_lib EmitZig where
  roots := #[`EmitZig, `InlineHelpers]

lean_lib EmitZigTests where
  roots := #[`test]

@[default_target]
lean_exe emitzig where
  root := `Main

@[test_driver]
lean_exe emitzig_tests where
  root := `EmitZigTest
