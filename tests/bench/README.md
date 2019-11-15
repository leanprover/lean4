# Lean Benchmark Suites

This folder contains multiple small Lean programs for benchmarking used by two
separate benchmark suites based on the
[temci](https://github.com/parttimenerd/temci) benchmarking tool:
* The light-weight "Speedcenter" suite benchmarks the current build of Lean. It
  can be used for quick comparisons on the cmdline and powers the [Lean
  Speedcenter](http://speedcenter.informatik.kit.edu/lean/) website.
* The heavy-weight "Cross" suite benchmarks multiple Lean configurations and
  other functional compilers against each other and generates CSV and HTML
  reports from that. It was created for the paper "Counting Immutable Beans -
  Reference Counting Optimized for Purely Functional Programming" (IFL19).

## Speedcenter Suite

Requirements:
* A local Lean build in `../../build/release`. Build at least the `bin` target.
* temci. Using [Nix](https://nixos.org/nix/), open a nix-shell in the project
  root directory to add a compatible version to your PATH. Alternatively, try
  `pip3 install git+https://github.com/parttimenerd/temci.git`.

To execute the suite and save the results in `base.yaml`, run (in this folder)
```
temci exec --config speedcenter.yaml --out base.yaml
```
Other interesting `exec` flags:
* use `--runs N` to modify the default number of 10 runs per benchmark
* use `--included_blocks fast` to excluded slow benchmarks like the stdlib
  benchmark. You can replace `fast` with any benchmark name or label in
  `speedcenter.exec.yaml`.

If you have multiple saved result files, you can compare them with
```
temci report --config speedcenter.yaml report1.yaml report2.yaml ...
```

## Cross Suite

We recommend using [Nix](https://nixos.org/nix/) for building/obtaining all Lean variants and used
compilers in a reproducible way. After installing Nix, running the benchmarks is as easy as

```
nix-shell cross.nix --pure --run make
```

This will record 50 runs for each benchmark configuration (this can be changed with `runs` in `cross.yaml`),
generate results in `report_lean.csv` and `report_cross.csv`, and print them to stdout in a tabulated format.
It will also generate HTML reports in `report/` comparing the time-based benchmarks.

In order to reduce noise in the benchmarking data, you may instead want to try calling `make` inside a
temci shell:

```
nix-shell cross.nix --pure --run "temci short shell --sudo --preset usable --cpuset_active make"
```

Using root powers, this will temporarily configure your machine similarly to the
[LLVM benchmarking recommendations](https://llvm.org/docs/Benchmarking.html) and move all your other
processes to a single CPU core.
