/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

private builtin_initialize importingRef : IO.Ref Bool ← IO.mkRef false

private builtin_initialize runInitializersRef : IO.Ref Bool ← IO.mkRef false

/--
By default the `initialize` code is not executed when importing .olean files.
When this flag is set to `true`, the initializers are executed.
This method is meant to be used by the Lean frontend only.
Remark: it is not safe to run `initialize` code when using multiple threads.
Remark: Any loaded native Lean code must match its imported version. In particular,
  no two versions of the same module may be loaded when this flag is set.
  No native code may be loaded after its module has been imported.
Remark: Compacted module regions must not be freed when using this flag as the
  cached initializer results may reference objects in them.
Remark: The Lean frontend executes this method at startup time.
-/
@[export lean_enable_initializer_execution]
unsafe def enableInitializersExecution : IO Unit :=
  runInitializersRef.set true

def isInitializerExecutionEnabled : IO Bool :=
  runInitializersRef.get

/--
We say Lean is "initializing" when it is executing `builtin_initialize` declarations or importing modules.
Recall that Lean executes `initialize` declarations while importing modules.
-/
def initializing : IO Bool :=
  IO.initializing <||> importingRef.get

/--
Execute `x` with "importing" flag turned on.
When the "importing" flag is set to true, we allow user-extensions defined with with
the `initialize` command to update global references.
IMPORTANT: There is no semaphore controlling the access to these global references.
We assume these global references are updated by a single execution thread.
This is true in the Lean frontend where we process the `import` commands at the beginning
of the execution only. Users must make sure that when `importModules` is used, there is only
one execution thread accessing the global references.
-/
def withImporting (x : IO α) : IO α :=
  try
    importingRef.set true
    x
  finally
    importingRef.set false
    runInitializersRef.set false

end Lean
