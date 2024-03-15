# Language Server

This directory contains the implementation of the Lean Language Server, an implementation as well as extension of the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) used for communicating with Lean extensions in editors.

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

The actual processing of the opened file is left to the `Lean.Language.Lean` processor.
The interface is shared with the cmdline driver that is used for building Lean files but the core concept of *snapshots* produced by a processor is mostly of interest to the worker: snapshots are how processing data is saved and reused between versions of a file such as to make processing on file edits incremental.
How exactly incrementality is implemented is left completely to the processor; in a strictly ordered language like Lean, there may be a chain of snapshots for each top-level command, potentially with nested snapshots for increased granularity of incrementality.
In languages with less strict ordering and less syntax extensibility, there may be a single snapshot for the full syntax tree of the file, and then nested snapshots for processing each declaration in it.
In the simplest case, there may be a single snapshot after processing the full file, without any incrementality.
All the worker needs to know is that `Lean.Language.Lean.process` returns a root snapshot of some type that can be transformed into an asynchronously constructed tree of the generic `Lean.Language.Snapshot` type via `Lean.Language.ToSnapshotTree`.
We use a tree and not an asynchronous list (which would basically be a channel) in order to accommodate parallel processing where it's not clear a priori which of a number of child snapshots will be available first.
After loading the file and after each edit, the server will obtain this tree from the processor given the new file content and asynchronously wait on all its nodes and report the processing status (diagnostics and progress information) stored therein to the client incrementally (`Lean.Server.FileWorker.reportSnapshots`).

(TODO: the remainder is currently hard-coded for the `Lean` language)

Request handlers usually locate and access a single snapshot in the tree based on the cursor position using `withWaitFindSnap`, which will wait for elaboration if it is not sufficiently progressed yet.
After the snapshot is available, they can access its data, in particular the command's `Syntax` tree and elaboration `InfoTree`, in order to respond to the request.

The `InfoTree` is the second central server metadata structure.
It is filled during elaboration with various metadata that cannot (easily) be recovered from the kernel declarations in the environment: goal & subterm infos including the precise local & metavariable contexts used during elaboration, macro expansion steps, ...
Once a relevant `Snapshot` `snap` has been located, `snap.infoTree.smallestInfo?` and other functions from `Lean.Server.InfoUtils` can be used to further locate information about a document position.
The command `set_option trace.Elab.info true` instructs Lean to display the `InfoTree` for the declarations occurring after it.

### Communication

The asynchronous nature of the file worker complicates communication.
As mentioned above, a language processor does not directly talk to the worker but merely places diagnostics in the asynchronously constructed tree of snapshots where they will be picked up by the reporting task in the worker.
From there the diagnostics are passed to the channel `WorkerContext.chanOut` read by a single dedicated thread and finally written to stdout, which ensures that reporting tasks from multiple document versions cannot race on the eventual output.
Request responses are sent to this channel as well.

A further complication in communication is interactive diagnostics, which unlike most Lean objects have relevant *identity* as the client can hold references to them, and replacing an interactive diagnostic with an equal but not identical diagnostic can lead to the client reloading the view and losing local state such as the unfolding of a trace tree.
Thus we have to make sure that when we reuse snapshots, we reuse interactive diagnostic objects as is.
On the other hand, we do not want language processors to think about interactive diagnostics for simplicity and module dependency reasons, so we transform diagnostics into interactive ones in the reporting task in the worker and have language processors merely store a dynamic `IO.Ref` in `Snapshot.Diagnostics` that the reporting task then uses to store and reuse interactive diagnostics.
We initially stored unique IDs in `Snapshot.Diagnostics` for this that would be associated with the cached value in a map in the worker but there was no practical upside to this additional bookkeeping overhead.

## Code style

Comments should exist to denote specifics of our implementation but, for
the most part, we shouldn't copy comments over from the LSP specification
to avoid unnecessary duplication.
