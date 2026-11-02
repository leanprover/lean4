import Std.Tactic.BVDecide

/-!
The bytecode literals of the `Lean.KernelVM` programs in the library are the compiled versions of
their structured programs.
-/

#guard Int.Internal.Linear.linCheckProg = Int.Internal.Linear.LinCheck.linCheckStmt.compile
#guard Std.Tactic.BVDecide.LRAT.KernelVM.lratVMProg = Std.Tactic.BVDecide.LRAT.KernelVM.lratVMStmt.compile
