# SiliquantFormalStudies — pure-Init Lean 4 formal theories (Moissanite-Labs/siliquant)

Self-contained, zero-dependency (`import`-free, pure `Init`) Lean 4 formal theory
package contributed from [Moissanite-Labs/siliquant](https://github.com/Moissanite-Labs/siliquant)
(`main`, `studies/`). **75 theorems across 10 modules**, all kernel-checked on
`leanprover/lean4:v4.36.0` with `lake build` — no `sorry`, no custom axioms, no
`native_decide`/`unsafe`/`partial`; `#print axioms` reports only the standard
`propext` / `Quot.sound` / `Classical.choice` (several exact witnesses depend on no
axioms at all).

## Modules

| Module | Theorems | Topic |
|---|---|---|
| `E8VsA16HadamardLaw` | 12 | Exact E8 vs A16 opposite-sign Hadamard law |
| `S70FormalTheory.CrossLayerNonAdditivity` | 7 | Cross-layer non-additivity of quantization error |
| `S70FormalTheory.RegimeTriangleMinimax` | 7 | Regime-triangle minimax |
| `S70FormalTheory.SortedBlockH4Optimality` | 7 | Sorted Block-H4 SwiGLU invariance/optimality |
| `S72bFormalTheory.BallBudgetCannibalization` | 7 | Two-level saddle point: ball-budget cannibalization |
| `S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction` | 7 | Cross-layer interference & BF16 obstruction |
| `S72bFormalTheory.TwoLevelSaddlePoint` | 7 | Two-level saddle-point theory |
| `S73bFormalTheory.HeavyTailLPTStarvation` | 7 | Heavy-tail greedy-LPT starvation |
| `S73bFormalTheory.LoadPowerCompressionPhase` | 7 | Load-power compression phase trichotomy |
| `S73bFormalTheory.LowBitrateAmplificationAndPareto` | 7 | Low-bitrate amplification & Pareto dominance |

## Build / verify

```bash
lake build          # leanprover/lean4:v4.36.0 (see lean-toolchain)
```

Each theorem is accompanied by `#print axioms <name>` at the end of its module.

## Provenance

Extracted verbatim (no edits) from the merged `studies/` bundles on
`Moissanite-Labs/siliquant@main` (PRs #87, #92, #94, #99), where each study also
ships a pure-Z/Q Python oracle, an adversarial test suite, and a SHA-256-pinned
certificate.
