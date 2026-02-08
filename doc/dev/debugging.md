Debugging
=========

Some notes on how to debug Lean, which may also be applicable to debugging Lean programs in general.

## Tracing

In `CoreM` and derived monads, we use `trace[traceCls] "msg with {interpolations}"` to fill the structured trace viewable with `set_option trace.traceCls true`.
New trace classes have to be registered using `registerTraceClass` first.

Notable trace classes:
* `Elab.command`/`Elab.step`: command/term macro expansion/elaboration steps

  Useful options modifying these traces for debugging syntax trees:
  ```
  set_option pp.raw true
  set_option pp.raw.maxDepth 10
  ```
* `Meta.synthInstance`: typeclass resolution
* `Meta.isDefEq`: unification
* `interpreter`: full execution trace of the interpreter. Only available in debug builds.

In pure contexts or when execution is aborted before the messages are finally printed, one can instead use the term `dbg_trace "msg with {interpolations}"; val` (`;` can also be replaced by a newline), which will print the message to stderr before evaluating `val`. `dbgTraceVal val` can be used as a shorthand for `dbg_trace "{val}"; val`.
Note that if the return value is not actually used, the trace code is silently dropped as well.

By default, such stderr output is buffered and shown as messages after a command has been elaborated, which is necessary to ensure deterministic ordering of messages under parallelism.
If Lean aborts the process before it can finish the command or takes too long to do that, using `-DstderrAsMessages=false` avoids this buffering and shows `dbg_trace` output (but not `trace`s or other diagnostics) immediately.

## Debuggers

`gdb`/`lldb` can be used to inspect stack traces of compiled Lean code, though they cannot print values of Lean variables and terms in any legible way yet.
For example, `b lean_panic_fn` can be used to look at the stack trace of a panic.

The [`rr` reverse debugger](https://github.com/rr-debugger/rr) is an amazing tool for investigating e.g. segfaults from reference counting errors, though better hope you will never need it...
