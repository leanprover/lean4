import Lean.Data.Lsp
open Lean.Lsp

def main (_ : List String) : IO Unit := do
  Ipc.runWith "lean" (#["--server"]) do
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
    Ipc.waitForWatchdogILeans 1
    Ipc.shutdown 2
    discard <| Ipc.waitForExit
