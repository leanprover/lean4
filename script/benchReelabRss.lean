import Lean.Data.Lsp
import Lean.Elab.Import
open Lean
open Lean.Lsp
open Lean.JsonRpc

/-!
Tests language server memory use by repeatedly re-elaborate a given file.

NOTE: only works on Linux for now.
-/

def main (args : List String) : IO Unit := do
  let leanCmd :: file :: iters :: args := args | panic! "usage: script <lean> <file> <#iterations> <server-args>..."
  let file ← IO.FS.realPath file
  let uri := s!"file://{file}"
  Ipc.runWith leanCmd (#["--worker", "-DstderrAsMessages=false"] ++ args ++ #[uri]) do
  -- for use with heaptrack:
  --Ipc.runWith "heaptrack" (#[leanCmd, "--worker", "-DstderrAsMessages=false"] ++ args ++ #[uri]) do
  --  -- heaptrack has no quiet mode??
  --  let _ ← (← Ipc.stdout).getLine
  --  let _ ← (← Ipc.stdout).getLine
    let capabilities := {
      textDocument? := some {
        completion? := some {
          completionItem? := some {
            insertReplaceSupport? := true
          }
        }
      }
    }
    Ipc.writeRequest ⟨0, "initialize", { capabilities : InitializeParams }⟩

    let text ← IO.FS.readFile file
    let (_, headerEndPos, _) ← Elab.parseImports text
    let headerEndPos := FileMap.ofString text |>.leanPosToLspPos headerEndPos
    let mut requestNo : Nat := 1
    let mut versionNo : Nat := 1
    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri := uri, languageId := "lean", version := 1, text := text } : DidOpenTextDocumentParams }⟩
    for i in [0:iters.toNat!] do
      if i > 0 then
        versionNo := versionNo + 1
        let params : DidChangeTextDocumentParams := {
          textDocument := {
            uri      := uri
            version? := versionNo
          }
          contentChanges := #[TextDocumentContentChangeEvent.rangeChange {
            start := headerEndPos
            «end» := headerEndPos
          } " "]
        }
        let params := toJson params
        Ipc.writeNotification ⟨"textDocument/didChange", params⟩
        requestNo := requestNo + 1

      let diags ← Ipc.collectDiagnostics requestNo uri versionNo
      if let some diags := diags then
        for diag in diags.param.diagnostics do
          IO.eprintln diag.message
      requestNo := requestNo + 1

      let status ← IO.FS.readFile s!"/proc/{(← read).pid}/status"
      for line in status.splitOn "\n" |>.filter (·.startsWith "RssAnon") do
        IO.eprintln line

    let _ ← Ipc.collectDiagnostics requestNo uri versionNo
    (← Ipc.stdin).writeLspMessage (Message.notification "exit" none)
    discard <| Ipc.waitForExit
