* The `MessageData.ofPPFormat` constructor has been removed.
  Its functionality has been split into two:

  - for lazy structured messages, please use `MessageData.lazy`;
  - for embedding `Format` or `FormatWithInfos`, use `MessageData.ofFormatWithInfos`.

  An example migration can be found in [#3929](https://github.com/leanprover/lean4/pull/3929/files#diff-5910592ab7452a0e1b2616c62d22202d2291a9ebb463145f198685aed6299867L109).

* The `MessageData.ofFormat` constructor has been turned into a function.
  If you need to inspect `MessageData`,
  you can pattern-match on `MessageData.ofFormatWithInfos`.

part of #3929
