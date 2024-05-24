# Reverse FFI (Fat Static Library)

This a simple example of how a Lake library (`lib/`) that has dependencies on multiple projects can be used from a foreign language and build system (`main.c` and `Makefile`).
This is achieved by building a single 'fat' static library that vendors all dependencies.

Note that in this example, `ExtraLib` is also linked into `libRFFIFat`, which can be confirmed by running `strings`.
This checks that `initialize_ExtraLib` is present in `libRFFIFat`, which would not be present in `libRFFI`.
