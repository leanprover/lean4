# Like `elab`, but without the deprecation linters (see `../README.md`).
LINTER_ARGS=(-Dlinter.all=false -Dlinter.deprecated.options=false -Dlinter.deprecated.arg=false -Dlinter.deprecated.module=false)
# The header snapshots are elaborated with the deprecation linters enabled.
LEAN_HEADER_SNAPSHOTS=0
source ../../elab/run_test.sh
