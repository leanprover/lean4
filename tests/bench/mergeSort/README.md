# mergeSortBenchmark

Benchmarking `List.mergeSort`.

Run `lake exe mergeSort k` to run a benchmark on lists of size `k * 10^5`.
This reports the average time (in milliseconds) to sort:
* an already sorted list
* a reverse sorted list
* an almost sorted list
* and a random list with duplicates

Run `python3 bench.py` to run this for `k = 1, .., 10`, and calculate a best fit
of the model `A * k + B * k * log k` to the observed runtimes.
(This isn't really what one should do:
fitting a log to data across a single order of magnitude is not helpful.)
