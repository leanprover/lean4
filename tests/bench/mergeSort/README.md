# mergeSortBenchmark

Benchmarking `List.mergeSort` and `Array.mergeSort`.

Run `lake exe mergeSort k` to run a benchmark on collections of size `k * 10^5`.

This reports the total and average time (in milliseconds) to sort both lists and arrays using 4 test cases:
* A reversed list/array (worst case for some algorithms)
* An already sorted list/array (best case)
* A random list/array with values 0-1000
* A partially sorted list/array with duplicates

The benchmark also reports the comparative performance (speedup) between the two implementations.

## Performance Characteristics

- **Small collections (< 100k elements)**: `List.mergeSort` is faster due to lower constant overhead
- **Medium collections (100k-500k elements)**: Performance is comparable, with crossover around 300-400k elements
- **Large collections (> 500k elements)**: `Array.mergeSort` is significantly faster (2-3.5x speedup at scale)

Run `python3 bench.py` to run this for `k = 1, .., 10`, and calculate a best fit
of the model `A * k + B * k * log k` to the observed runtimes.
(This isn't really what one should do:
fitting a log to data across a single order of magnitude is not helpful.)
