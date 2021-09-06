Using `perf`
------------

On Linux machines, we use `perf` + `hotspot` to profile `lean`.

Suppose, we are in the `lean4` root directory, and have a release build at `build/release`.
Then, we can collect profile data using the following command:

```
perf record --call-graph dwarf build/release/stage1/bin/lean src/Lean/Elab/Term.lean
```

Recall that, if you have `elan` installed in your system, `lean` is
actually the `elan` binary that selects which `lean` to execute.

To visualize the data, we use `hotspot`:

```
hotspot
```
