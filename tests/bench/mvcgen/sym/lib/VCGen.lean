/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public meta import VCGen.Reduce
public meta import VCGen.SpecDB
public meta import VCGen.RuleConstruction
public meta import VCGen.Context
public meta import VCGen.Util
public meta import VCGen.RuleCache
public meta import VCGen.Entails
public meta import VCGen.Solve
public meta import VCGen.Driver
public meta import VCGen.Frontend

/-!
The `mvcgen'` tactic, split across the modules above.

- `VCGen.Reduce` — SymM head-redex reducer.
- `VCGen.SpecDB` — `SpecTheoremNew`/`SpecTheoremsNew` + database operations.
- `VCGen.RuleConstruction` — SymM rule constructors from spec/simp/split info.
- `VCGen.Context` — `VCGenM`, its `Context`/`State`, the bundle of pre-built rules.
- `VCGen.Util` — generic VCGenM helpers (`introsSimp`, `repeatAndRfl`, app builders).
- `VCGen.RuleCache` — VCGenM cache wrappers around the SymM rule constructors.
- `VCGen.Entails` — entailment-shaped goal decomposition (`solveSPredEntails` etc.).
- `VCGen.Solve` — the main `solve` step / `SolveResult`.
- `VCGen.Driver` — the worklist driver (`work`, `emitVC`, `main`, `Result`).
- `VCGen.Frontend` — the `mvcgen'` syntax + tactic elaborator + `mkSpecContext`.
-/
