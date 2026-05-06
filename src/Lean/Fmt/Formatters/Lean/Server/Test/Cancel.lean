/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Server.Test.Cancel
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Server.Test.Cancel.commandWait_for_cancel_once_command_]
public def fmtWaitForCancelOnceCommand : Fmt := fun
  | `(Lean.Server.Test.Cancel.commandWait_for_cancel_once_command_|
      wait_for_cancel_once_command%$waitTk $n:num) => do
    let waitTk ← fmt waitTk
    let n ← fmt n
    return Layouts.pseudoApplication #[waitTk, n]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Server.Test.Cancel.tacticWait_for_test_task_]
public def fmtWaitForTestTask : Fmt := fun
  | `(Lean.Server.Test.Cancel.tacticWait_for_test_task_|
      wait_for_test_task%$waitTk $label:str) => do
    let waitTk ← fmt waitTk
    let label ← fmt label
    return Layouts.pseudoApplication #[waitTk, label]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Server.Test.Cancel.tacticWait_for_sync_]
public def fmtWaitForSync : Fmt := fun
  | `(Lean.Server.Test.Cancel.tacticWait_for_sync_| wait_for_sync%$waitTk $label:str) => do
    let waitTk ← fmt waitTk
    let label ← fmt label
    return Layouts.pseudoApplication #[waitTk, label]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Server.Test.Cancel.tacticBlock_until_cancelled_]
public def fmtBlockUntilCancelled : Fmt := fun
  | `(Lean.Server.Test.Cancel.tacticBlock_until_cancelled_|
      block_until_cancelled%$blockTk $label:str) => do
    let blockTk ← fmt blockTk
    let label ← fmt label
    return Layouts.pseudoApplication #[blockTk, label]
  | _ => throw .partialFormatter
