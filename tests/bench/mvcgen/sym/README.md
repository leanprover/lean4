# Benchmarks for a `Sym`-based `mvcgen`

Compares the performance of a `Sym`-based rewrite of `mvcgen` with that of a direct, hard-coded solution procedure (the `shallow_add_sub_cancel` benchmark).
To run the benchmarks, launch `lake build`.
To run individual benchmarks, run `lake lean vcgen_add_sub_cancel.lean` (which runs the VCGen-based version) or `lake lean baseline_add_sub_cancel.lean` (which runs the baseline hard-coded solution procedure).
