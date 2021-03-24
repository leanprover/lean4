## Building & Developing

Both watchdog and worker (see below) are part of the main `lean` binary.
If you only change the worker (true for most changes), the "refresh file dependencies" command of your editor will reload it after you rebuild `lean` (the rebuild happens automatically with the Nix setup, just be patient because there is no intermediate build output).
If you (also) change the watchdog, use the "restart server" command instead.

## Logging LSP requests

### In general

To log all LSP messages and server output into a directory, just set the `LEAN_SERVER_LOG_DIR` environment variable. This will create a file for each I/O stream of the main server process, as well as those of each worker process.

### In Emacs

See the `lsp-log-io` variable.

### In VSCode

Set `$extension.trace.server` to `verbose` as described in the *Usage* section of [LSP Inspector](https://microsoft.github.io/language-server-protocol/inspector/**.

## Server design

### (Very incomplete) notes on Lean 3

How the Lean 3 server provides info for mouse hovers, tactic states, widgets states and autocompletion:
- When compiling a file, the module manager stores *snapshots* of the environment and options
  after each command.
- The elaborator and certain tactics also register bits of information such as the elaborated types
  of expressions in an `info_manager`.
- When info is requested by the client, `server::info` at `src/shell/server.cpp:613` is called.
  It finds the closest snapshot to the position at which info is requested and passes
  that to `report_info` at `src/frontends/lean/interactive.cpp:141`. `report_info` queries
  the `info_manager` as well as the environment at that point for relevant information.

### Architecture

#### Process separation

The server consists of a single *watchdog* process coordinating per-file *worker* processes.

The watchdog's only purpose is to:
- manage a worker process for each open file;
- keep track of minimal persistent state;
- coalesce and coordinate the workers' communication with the LSP client.

Almost all of the actual computation (elaboration, `#eval`uation, autocompletion, ..) happens in the workers.

Why would we settle on such an architecture? The crucial point is that corruption of a single per-file worker cannot affect the stability of the whole server. A similar idea drove the design of per-tab sandbox processes in web browsers such as Chromium Site Isolation or Firefox Electrolysis. In our case though, possible corruption is not due to malicious behaviour (we assume Lean code opened in an editor is trusted) but rather due to arbitrary computation in metaprograms and `#eval` statements which users write. If the user code for one file causes a stack overflow, we would not want the entire server to die. Thanks to the separation, the offending file can be recompiled while keeping the state of other open files intact. To facilitate restarting workers in this fashion, the watchdog needs to keep track of a minimal amount of state - the contents of open files and possibly the place at which it crashed.

Another important consideration is the *compacted region* memory used by imported modules. For efficiency, these regions are not subject to the reference-counting GC and as such need to be freed manually when the imports change. But doing this safely is pretty much impossible, as safe freeing is the very problem GCs are supposed to solve. It is far easier to simply nuke and restart the worker process whenever this needs to be done, as it only happens in cases in which all of the worker's state would have to be recomputed anyway.

#### Recompilation of opened files

When the user has two or more files in a single dependency chain open, it is desirable for changes in imports to propagate to modules importing them. That is, when `B.lean` depends on `A.lean` and both are open, changes to `A` should eventually be observable in `B`. But a major problem with Lean 3 is how it does this much too eagerly. Often `B` will be recompiled needlessly as soon as `A` is opened, even if no changes have been made to `A`. For heavyweight modules which take up to several minutes to compile, this causes frustration when `A` is opened merely for inspection e.g. via go-to-definition.

In Lean 4, the situation is different as `.olean` artifacts are required to exist for all imported modules -- one cannot import a `.lean` file without compiling it first. In the running example, when a user opens and edits `A`, nothing is going to happen to `B`. They can continue to interact with it as if `A` kept its previous contents. But when `A` is saved with changes, `.olean` compilation will be triggered (user-configurable, can be disabled) and correspondingly `B` will be recompiled. This being a conscious action, users will be aware of having to then wait for reverse dependencies to recompile.

### Code style

Comments should exist to denote specifics of our implementation but, for
the most part, we shouldn't copy comments over from the LSP specification
to avoid unnecessary duplication.
