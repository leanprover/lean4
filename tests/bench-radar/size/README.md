# The `size` benchmark

This benchmark measures the number and size of a few kinds of files.
It expects to be executed after the `stdlib` benchmark.

The following general metrics are collected:

- `size/libleanshared.so//bytes`

The following metrics are collected for the entirety of stdlib:

- `size/stdlib/.c//files`
- `size/stdlib/.c//lines`
- `size/stdlib/.cpp//files`
- `size/stdlib/.cpp//lines`
- `size/stdlib/.lean//files`
- `size/stdlib/.lean//lines`
- `size/stdlib/.ilean//files`
- `size/stdlib/.ilean//bytes`
- `size/stdlib/.olean//files`
- `size/stdlib/.olean//bytes`
- `size/stdlib/.olean.server//files`
- `size/stdlib/.olean.server//bytes`
- `size/stdlib/.olean.private//files`
- `size/stdlib/.olean.private//bytes`
- `size/stdlib/.ir//files`
- `size/stdlib/.ir//bytes`

The following metrics are collected only for the `Init` library.

- `size/init/.olean//files`
- `size/init/.olean//bytes`
- `size/init/.olean.server//files`
- `size/init/.olean.server//bytes`
- `size/init/.olean.private//files`
- `size/init/.olean.private//bytes`
