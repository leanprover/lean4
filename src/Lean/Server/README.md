## Logging LSP requests

### In `bash`:

```
mkfifo pipe
nc -l -p 12345 < pipe | tee client.log | ./build/bin/Server 2> stderr | tee pipe server.log
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
