# cachePrivateImport

This test checks that the language server can import a module when the artifacts of its private
imports are only in the Lake artifact cache. It is the regression test for
[#14435](https://github.com/leanprover/lean4/issues/14435).

The language server loads the IR of every transitive import, including modules that are reachable
only through private imports. When the build directory contains only traces, Lean finds those
artifacts through the `importArts` map produced by `lake setup-file`.

## Files

Each arrow is a private `import`.

```
 opened by the server                  built by `lake build Lib`
+-----------------------+
| Test.lean             |
| outside every library |---+
+-----------------------+   |     +----------+     +------------+     +------------+
                            +---->| Lib.lean |---->| Lib/A.lean |---->| Lib/C.lean |
+--------------------+      |     +----------+     +------------+     +------------+
| Lib/B.lean         |------+      direct           one private        two private
| library module not |             import of        import away        imports away
| imported by `Lib`  |             both files
+--------------------+
```

The server opens `Test.lean` as a file that is external to the workspace and `Lib/B.lean` as an
edited module of the workspace. `Lib.A` and `Lib.C` are reachable only through private imports.

`lakefile.toml` declares the library `Lib`, and `clean.sh` removes the build directory, the local
cache, and the test output.

## Steps in `test.sh`

1. `LAKE_CACHE_DIR` points at `.lake/cache`, so the test uses its own cache.
   `LAKE_ARTIFACT_CACHE=true` turns the cache on, and unsetting `LAKE_RESTORE_ARTIFACTS` keeps
   Lake from copying artifacts back into the build directory.
2. `lake build Lib` fills the cache. Removing `.lake/build` and building again restores the build
   from the cache, which leaves only traces in the build directory.
3. The two `test_exp` lines check that the `.ir.sig` files of `Lib.A` and `Lib.C` are absent from
   the build directory. Lean falls back to the build directory for a module that is missing from
   `importArts`, so these checks make sure that the later steps depend on `importArts`.
4. `lean -DElab.inServer=true Test.lean` runs without a setup and has to fail. This shows that Lean
   can't load the imports from the build directory alone.
5. For `Test.lean` and `Lib/B.lean`, `lake setup-file` writes the setup to `.lake/setup.json`. The
   two `grep` lines check that the setup lists `Lib.A` and `Lib.C`.
6. `lean --setup .lake/setup.json -DElab.inServer=true` elaborates the header of the same file. The
   language server sets `Elab.inServer` itself, and the flag makes a command-line `lean` import at
   the same level.
7. `lake lean -v Test.lean` logs the setup of a command-line run. The check that `"Lib.A"` is
   absent makes sure that the wider artifact set is limited to the server. The check that
   `"importArts":{"Lib"` is present makes sure that the log contains the setup.
