import Lean.Data.Lsp
import Lean.Elab.Import
open Lean
open Lean.Lsp
open Lean.JsonRpc

/-!
Tests watchdog memory use by repeatedly re-elaborate a given file.

NOTE: only works on Linux for now.
-/

def determineRSS (pid : UInt32) : IO Nat := do
  let status ← IO.FS.readFile s!"/proc/{pid}/status"
  let some rssLine := status.splitOn "\n" |>.find? (·.startsWith "RssAnon:")
    | throw <| IO.userError "No RSS in proc status"
  let rssLine := rssLine.dropPrefix "RssAnon:"
  let rssLine := rssLine.dropWhile Char.isWhitespace
  let some rssInKB := rssLine.takeWhile Char.isDigit |>.toNat?
    | throw <| IO.userError "Cannot parse RSS"
  let rss := 1024*rssInKB
  return rss

def main (args : List String) : IO Unit := do
  let leanCmd :: file :: iters :: args := args | panic! "usage: script <lean> <file> <#iterations> <server-args>..."
  let file ← IO.FS.realPath file
  let uri := s!"file://{file}"
  Ipc.runWith leanCmd (#["--server", "-DstderrAsMessages=false"] ++ args ++ #[uri]) do
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
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    let text ← IO.FS.readFile file
    let (_, headerEndPos, _) ← Elab.parseImports text
    let headerEndPos := FileMap.ofString text |>.leanPosToLspPos headerEndPos
    let n := iters.toNat!
    let mut lastRSS? : Option Nat := none
    let mut totalRSSDelta : Int := 0
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

      Ipc.waitForILeans requestNo uri versionNo

      let rss ← determineRSS (← read).pid
      if let some lastRSS := lastRSS? then
        totalRSSDelta := totalRSSDelta + ((rss : Int) - (lastRSS : Int))
      lastRSS? := some rss

    let avgRSSDelta := totalRSSDelta / (n - 1)
    IO.println s!"avg re-elab RSS delta: {avgRSSDelta} B"

    let _ ← Ipc.collectDiagnostics requestNo uri versionNo
    Ipc.shutdown requestNo
    discard <| Ipc.waitForExit
