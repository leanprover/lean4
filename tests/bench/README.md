# Lean Benchmark Suite

This folder contains multiple small Lean programs for benchmarking and comparing their performance
to other Lean configurations and functional compilers using the
[temci](https://github.com/parttimenerd/temci) benchmarking tool.

We recommend using [Nix](https://nixos.org/nix/) for building/obtaining all Lean variants and used
compilers in a reproducible way. After installing Nix, running the benchmarks is as easy as

```
nix-shell --run make
```

This will record 50 runs for each benchmark configuration (this can be changed with `min_runs` in `temci.yaml`),
generate results in `report_lean.csv` and `report_cross.csv`, and print them to stdout in a tabulated format.
It will also generate HTML reports in `report/` comparing the time-based benchmarks.

In order to reduce noise in the benchmarking data, you may instead want to try calling `make` inside a
temci shell:

```
nix-shell --run "temci short shell --sudo --preset usable --cpuset_active make"
```

Using root powers, this will temporarily configure your machine similarly to the
[LLVM benchmarking recommendations](https://llvm.org/docs/Benchmarking.html) and move all your other
processes to a single CPU core.
