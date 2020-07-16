## Building

(Assuming `lean4` is the `elan` toolchain for stage 0.5)
```
leanmake +lean4 bin PKG=ServerBin LINK_OPTS=-rdynamic
```

## Logging LSP requests

### In `bash`:

```
mkfifo pipe
# So that the server can find and import packages
export LEAN_PATH=$LEAN4_HOME/build/$RELEASE_OR_DEBUG/stage0.5/lib/lean/
nc -l -p 12345 < pipe | tee client.log | ./build/bin/ServerBin 2> stderr | tee pipe server.log
```
will create three files to follow with `tail -f` -- `client.log` for client messages, `server.log` for server messages and `stderr` for server `IO.stderr` debugging

### In VSCode

Set `$extension.trace.server` to `verbose` as described in the *Usage* section of [LSP Inspector](https://microsoft.github.io/language-server-protocol/inspector/).

An easy way to get an LSP client is to build the [sample extension](https://github.com/Microsoft/vscode-extension-samples/tree/master/lsp-sample) and replace the server options in `extension.ts`:

```typescript
  let serverOptions: ServerOptions = {
    command: "/usr/bin/nc",
    args: ["localhost", "12345"],
    options: null
  };
```

## Known issues affecting development

- https://leanprover.zulipchat.com/#narrow/stream/147302-lean4/topic/segfaulting.20lean.20binary

## (Very incomplete) notes on Lean 3

How the Lean 3 server provides info for mouse hovers, tactic states, widgets states and autocompletion:
- When compiling a file, the module manager stores *snapshots* of the environment and options
  after each command.
- The elaborator and certain tactics also register bits of information such as the elaborated types
  of expressions in an `info_manager`.
- When info is requested by the client, `server::info` at `src/shell/server.cpp:613` is called.
  It finds the closest snapshot to the position at which info is requested and passes
  that to `report_info` at `src/frontends/lean/interactive.cpp:141`. `report_info` queries
  the `info_manager` as well as the environment at that point for relevant information.
