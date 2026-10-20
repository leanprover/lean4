# Test data

`basic.txt` holds a small set of decimal-to-float vectors in the
[`parse-number-fxx-test-data`](https://github.com/nigeltao/parse-number-fxx-test-data)
format and is what `lake exe parse-number-check` checks when given no directory
argument. It covers a handful of basic conversions and confirms that the vector
parser itself works (comments, blank lines, the various decimal forms, and the
four space-separated fields).

`random-from-dataset.txt` contains 10,000 random test cases (out of more than 5 million)
from the aforementioned repository.

`doubleround.txt` contains some difficult subnormal cases which detect double-rounding
issues in the conversion routine.

Each non-blank, non-comment line has four space-separated fields:

    <binary16-hex> <binary32-hex> <binary64-hex> <decimal-string>

the correctly rounded (round-to-nearest, ties-to-even) `binary16`, `binary32`,
and `binary64` bit patterns of the decimal value in the fourth field. The
harness ignores the `binary16` field and checks the `OfScientific Float` and
`OfScientific Float32` instances against the `binary64` and `binary32` fields.

To run against the full upstream suite instead, clone that repository and point
the executable at its `data/` directory:

    lake exe parse-number-check /path/to/parse-number-fxx-test-data/data
