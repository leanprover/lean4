Fixing Tests
============

The test suite contains some tests that compare the produced output
with the expected output. For example, the directory `tests/lean`
contains files such as [`bad_class.lean`](../tests/lean/bad_class.lean) and
[`bad_class.lean.expected.out`](../tests/lean/bad_class.lean.expected.out).
The later contains the expected output for the test file `bad_class.lean`.

When the Lean source code or the standard library are modified, some of these
tests break because the produced output is slightly different, and we have
to reflect the changes in the `.lean.expected.out` files.
We should not blindly copy the new produced output since we may accidentally
miss a bug introduced by recent changes.
The test suite contains commands that allow us to see what changed in a convenient way.
First, we must install [meld](http://meldmerge.org/). On Ubuntu, we can do it by simply executing

```
sudo apt-get install meld
```

Now, suppose `bad_class.lean` test is broken. We can see the problem by going to `test/lean` directory and
executing

```
./test_single.sh -i bad_class.lean
```

When the `-i` option is provided, `meld` is automatically invoked
whenever there is discrepancy between the produced and expected
outputs. `meld` can also be used to repair the problems.

In Emacs, we can also execute `M-x lean4-diff-test-file` to check/diff the file of the current buffer.
To mass-copy all `.produced.out` files to the respective `.expected.out` file, use `tests/lean/copy-produced`.
When using the Nix setup, add `--keep-failed` to the `nix build` call and then call
```sh
tests/lean/copy-produced <build-dir>/source/tests/lean
```
instead where `<build-dir>` is the path printed out by `nix build`.
