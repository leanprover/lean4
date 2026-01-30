# The `size` benchmark

This benchmark measures the number and size of a few kinds of files.
It expects to be executed after the `build` benchmark.

The following general metrics are collected:

- `size/libleanshared.so//bytes`
- `size/libleanshared.so//dynamic symbols`
- `size/libLake_shared.so//dynamic symbols`

The following metrics are collected from the entire build process:

- `size/all/.c//files`
- `size/all/.c//lines`
- `size/all/.cpp//files`
- `size/all/.cpp//lines`
- `size/all/.lean//files`
- `size/all/.lean//lines`
- `size/all/.ilean//files`
- `size/all/.ilean//bytes`
- `size/all/.olean//files`
- `size/all/.olean//bytes`
- `size/all/.olean.server//files`
- `size/all/.olean.server//bytes`
- `size/all/.olean.private//files`
- `size/all/.olean.private//bytes`
- `size/all/.ir//files`
- `size/all/.ir//bytes`

The following metrics are collected only for the `Init` library.

- `size/init/.olean//files`
- `size/init/.olean//bytes`
- `size/init/.olean.server//files`
- `size/init/.olean.server//bytes`
- `size/init/.olean.private//files`
- `size/init/.olean.private//bytes`

The following metric measures the size of all files produced by a `make install`.

- `size/install//bytes`
