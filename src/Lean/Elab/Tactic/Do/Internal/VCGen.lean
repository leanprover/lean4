/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.EPost
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails
public import Lean.Elab.Tactic.Do.Internal.VCGen.Solve
public import Lean.Elab.Tactic.Do.Internal.VCGen.Driver
public import Lean.Elab.Tactic.Do.Internal.VCGen.Frontend

/-!
The `vcgen` tactic, split across the modules above.

- `VCGen.Reduce` — SymM head-redex reducer.
- `VCGen.SpecDB` — `SpecTheorem` instantiation, simp-side migration, and `findSpecs` lookup.
- `VCGen.RuleConstruction` — SymM rule constructors from spec/simp/split info.
- `VCGen.Context` — `VCGenM`, its `Context`/`State`, the bundle of pre-built rules.
- `VCGen.EPost` — exception-postcondition decomposition helpers.
- `VCGen.Util` — generic VCGenM helpers (`introsHygienic`, `simpGoalTelescope`, `solveTrivialConjuncts`).
- `VCGen.RuleCache` — VCGenM cache wrappers around the SymM rule constructors.
- `VCGen.Entails` — entailment-shaped goal decomposition (Triple unfolding, state/precondition intro, EPost and lattice steps).
- `VCGen.Solve` — the main `solve` step / `SolveResult`.
- `VCGen.Driver` — the worklist driver (`work`, `emitVC`, `main`, `Result`).
- `VCGen.Frontend` — the `vcgen` syntax + tactic elaborator + `mkSpecContext`.
-/
