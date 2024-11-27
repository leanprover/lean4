import Lean

run_meta Lean.Compiler.compile #[``Lean.Elab.Structural.structuralRecursion, ``Lean.Elab.Command.elabInductives, ``Lean.Environment.displayStats, ``Lean.Meta.IndPredBelow.mkBelow, ``unexpandExists]
