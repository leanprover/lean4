Fixing Tests
============

The test suite contains some tests that compare the produced output
with the expected output. For example, the directory `tests/lean`
contains files such as [`bad_class.lean`](../tests/lean/bad_class.lean) and
[`bad_class.lean.expected.out`](../tests/lean/bad_class.lean.expected.out).
The later contains the expected output for the test file `bad_class.lean`.

When the Lean source code or the standard library are modified, some of these
tests break because the produced output is slightly different, and we have
to reflect the changes int the `.lean.expected.out` files.
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
./test_single.sh ../../bin/lean bad_class.lean yes
```

When the `yes` option is provided, `meld` is automatically invoked
whenever there is discrepancy between the produced and expected
outputs. `meld` can also be used to repair the problems.

Here is the list of directories where produced output is compared with
the expected output (stored in a `*.expected.out` file).

- [`tests/lean`](../tests/lean)
- [`tests/lean/interactive`](../tests/lean/interactive)

Remark: in the directory `tests/lean/interactive`, the input test files have extension `.input`.
They simulate commands sent from Emacs to Lean.
The `.lean` files in this directory are used to simulate files opened by the user.