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

Set `$extension.trace.server` to `verbose` as described in the [Language Server Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide#logging-support-for-language-server).

## Server design

### Process separation

The server consists of a single *watchdog* process coordinating per-file *worker* processes.

The watchdog's only purpose is to:
- manage a worker process for each open file;
- keep track of minimal persistent state;
- coalesce and coordinate the workers' communication with the LSP client.

Almost all of the actual computation (elaboration, `#eval`uation, autocompletion, ..) happens in the workers.

Why would we settle on such an architecture? The crucial point is that corruption of a single per-file worker cannot affect the stability of the whole server. A similar idea drove the design of per-tab sandbox processes in web browsers such as Chromium Site Isolation or Firefox Electrolysis. In our case though, possible corruption is not due to malicious behaviour (we assume Lean code opened in an editor is trusted) but rather due to arbitrary computation in metaprograms and `#eval` statements which users write. If the user code for one file causes a stack overflow, we would not want the entire server to die. Thanks to the separation, the offending file can be recompiled while keeping the state of other open files intact. To facilitate restarting workers in this fashion, the watchdog needs to keep track of a minimal amount of state - the contents of open files and possibly the place at which it crashed.

Another important consideration is the *compacted region* memory used by imported modules. For efficiency, these regions are not subject to the reference-counting GC and as such need to be freed manually when the imports change. But doing this safely is pretty much impossible, as safe freeing is the very problem GCs are supposed to solve. It is far easier to simply nuke and restart the worker process whenever this needs to be done, as it only happens in cases in which all of the worker's state would have to be recomputed anyway.

### Recompilation of opened files

When the user has two or more files in a single dependency chain open, it is desirable for changes in imports to propagate to modules importing them. That is, when `B.lean` depends on `A.lean` and both are open, changes to `A` should eventually be observable in `B`. But a major problem with Lean 3 is how it does this much too eagerly. Often `B` will be recompiled needlessly as soon as `A` is opened, even if no changes have been made to `A`. For heavyweight modules which take up to several minutes to compile, this causes frustration when `A` is opened merely for inspection e.g. via go-to-definition.

In Lean 4, the situation is different as `.olean` artifacts are required to exist for all imported modules -- one cannot import a `.lean` file without compiling it first. In the running example, when a user opens and edits `A`, nothing is going to happen to `B`. They can continue to interact with it as if `A` kept its previous contents. But when `A` is saved with changes, users can then issue the "refresh file dependencies" command in their editor, which will restart the respective worker and use `lake setup-file` to rebuild and locate its dependencies. This being a conscious action, users will be aware of having to then wait for compilation.

### Worker architecture

A central concept in the worker is the *snapshot*.
Lean files are processed (elaborated) strictly from top to bottom, with each command being fully processed before processing of subsequent commands is started.
The worker implements this same processing order, but saves a `Snapshot` of the entire elaboration state after the imports and each command, which is cheap and easy to do because the state is all functional data structures.
Thanks to these snapshots, we can restart processing the file at the point of a change by discarding and rebuilding all snapshots after it.
Snapshots are computed asynchronously and stored in an `AsyncList`, which is a list whose tail is potentially still being processed.
Request handlers usually locate and access a single snapshot in the list based on the cursor position using `withWaitFindSnap`, which will wait for elaboration if it is not sufficiently progressed yet.
After the snapshot is available, they can access its data, in particular the command's `Syntax` tree and elaboration `InfoTree`, in order to respond to the request.

The `InfoTree` is the second central server data structure.
It is filled during elaboration with various metadata that cannot (easily) be recovered from the kernel declarations in the environment: goal & subterm infos including the precise local & metavariable contexts used during elaboration, macro expansion steps, ...
Once a relevant `Snapshot` `snap` has been located, `snap.infoTree.smallestInfo?` and other functions from `Lean.Server.InfoUtils` can be used to further locate information about a document position.
The command `set_option trace.Elab.info true` instructs Lean to display the `InfoTree` for the declarations occurring after it.

## Code style

Comments should exist to denote specifics of our implementation but, for
the most part, we shouldn't copy comments over from the LSP specification
to avoid unnecessary duplication.
