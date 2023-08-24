# Stress test for lake

This repo "accurately" simulates the contents of mathlib
to help with performance optimizations in Lake.

```bash
time lake build
```

## Variations

The contents of this repository are automatically generated.
You can also try different parameters:

```bash
lake run mk 40 40
```

These are the default values.
The first number is the maximum dependency depth,
the second number is the number of dependencies for each file.

## Credits

This test is a fork of Gabriel Ebner's [GitHub repository](https://github.com/gebner/inundation/tree/master). Thank him for the initial idea!
