# mergeSortBenchmark

Benchmarking `List.mergeSort` and `Array.mergeSort`.

Run `lake exe mergeSort k` to run a benchmark on collections of size `k * 10^5`.
This reports the total and average time (in milliseconds) to sort:
* an already sorted list/array
* a reverse sorted list/array
* an almost sorted list/array
* and a random list/array with duplicates

The benchmark also reports the comparative performance between the two implementations.

## Performance Characteristics

In many cases, `List.mergeSort` is faster. However, for large, random collections (>= 600k elements), `Array.mergeSort` scales better.

Run `python3 bench.py` to run this for `k = 1, .., 10`, and calculate a best fit
of the model `A * k + B * k * log k` to the observed runtimes.
(This isn't really what one should do:
fitting a log to data across a single order of magnitude is not helpful.)

More detailed comparisons can be generated using `python3 bench2.py`.
