Lean binary distribution
------------------------

The binary distribution package contains:

- Lean executable (located in the sub-directory bin)
- Standard library (located in the sub-directory lib/lean/library)
- HoTT library (located in the sub-directory lib/lean/hott)
- Emacs modes (located in the sub-directory share/emacs/site-list/lean)

Assuming you are in the same directory this file is located,
the following command executes a simple set of examples

% bin/lean examples/ex.lean

The Emacs mode is the ideal way to use Lean. It requires at
least Emacs version 24.3

Documentation
-------------

The tutorial "Theorem Proving in Lean" describes Lean main features,
and provides many examples. The tutorial is available in two different forms:

 - Interactive HTML: http://leanprover.github.io/tutorial/index.html
 - PDF: http://leanprover.github.io/tutorial/tutorial.pdf

Command line options
--------------------

Here are some useful commands for users that do not want to use Emacs,
or prefer command line tools.

- `-T` do not type check imported .olean files

  % bin/lean -T examples/ex.lean

The option can save you a significant amount of time if you are importing
many files. Lean still checks the check-sum of the imported files.
So, it still can detect trivial tempering of the .olean files.

- `-c [file.clean]` create/use a cache file. This option can increase the
compilation time of large files when we are invoking Lean many times
with small incremental changes.

  % bin/lean -c ex.clean examples/ex.lean

- `--deps` display files imported by a given Lean file. This option
is useful if you want to build your own custom Makefile.

  % bin/lean --deps examples/ex.lean
