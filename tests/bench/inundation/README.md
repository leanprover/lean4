# Stress Test for Lake

This folder generates a deeply nested import tree of Lean modules
that can then be used as a stress test of large Lake builds (e.g., Mathlib).
The modules lack any code.

This removes variations in Lean elaboration time as a confounding factor,
but also means this test cannot be used to profile features that depend on code size
(e.g., OLean hashing or a module system).

## Usage

This folder is tested as part of Lean's speed center benchmarks,
but it can also be run manually like so:

```bash
lake run mk
time lake build
```

These commands generate the mock source files and then time the build.

## Variations

The source generation configuration is flexible:

```bash
lake run -Ktest=Test mk 40 40
```

The `test` option is which subdirectory of the `Inundation` source directory to output files.
The first number is the maximum dependency depth,
the second number is the number of dependencies for each file.
The settings above are the default values.

## Credits

This test is a fork of Gabriel Ebner's [GitHub repository](https://github.com/gebner/inundation/tree/master). Thank him for the initial idea!
