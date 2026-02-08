/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Std.OperatingSystemAbstractions.AsynchronousIO
import GroveStdlib.Std.OperatingSystemAbstractions.BasicIO
import GroveStdlib.Std.OperatingSystemAbstractions.ConcurrencyAndParallelism
import GroveStdlib.Std.OperatingSystemAbstractions.EnvironmentFileSystemProcesses
import GroveStdlib.Std.OperatingSystemAbstractions.Locales

open Grove.Framework Widget

namespace GroveStdlib.Std

namespace OperatingSystemAbstractions

end OperatingSystemAbstractions

def operatingSystemAbstractions : Node :=
  .section "operating-system-abstractions" "Operating system abstractions" #[
    OperatingSystemAbstractions.asynchronousIO,
    OperatingSystemAbstractions.basicIO,
    OperatingSystemAbstractions.concurrencyAndParallelism,
    OperatingSystemAbstractions.environmentFileSystemProcesses,
    OperatingSystemAbstractions.locales
  ]

end GroveStdlib.Std
