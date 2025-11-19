/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
import Lean.Server.FileWorker.WidgetRequests
import Lean.Widget.UserWidget

/-!
This file includes a complete overview over the Lean LSP API for documentation purposes.
-/

namespace Lean.Server.Overview

open Lean.JsonRpc Lean.Lsp Lean.Widget

inductive ProtocolExtensionKind
  | standard
  | leanSpecificMethod
  | extendedParameterType (fieldNames : Array Name)
  | extendedResponseType (fieldNames : Array Name)
  | extendedParameterAndResponseType (parameterFieldNames responseFieldNames : Array Name)
  | standardViolation (description : String)

structure RequestOverview where
  method : String
  direction : MessageDirection
  kinds : Array ProtocolExtensionKind
  parameterType : Type
  responseType : Type
  description : String

structure RpcRequestOverview where
  method : Name
  parameterType : Type
  responseType : Type
  description : String

structure NotificationOverview where
  method : String
  direction : MessageDirection
  kinds : Array ProtocolExtensionKind
  parameterType : Type
  description : String

inductive MessageOverview where
  | request (o : RequestOverview)
  | rpcRequest (o : RpcRequestOverview)
  | notification (o : NotificationOverview)

opaque NestedType (outerToInner : Array Type) : Type

/--
Complete overview over the full Lean LSP API.

The Lean language server requires all files for which it receives requests and notifications
to be opened by a `textDocument/didOpen` notification first, i.e. for the language client
to fully manage the contents of all files.
It will discard notifications and error requests for closed files.
This is in violation with LSP, which leaves the possibility open for language servers to receive
requests for open files, but this violation does not create problems with either VS Code or NeoVim.
-/
def protocolOverview : Array MessageOverview := #[
  .notification {
    method := "$/cancelRequest"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CancelParams
    description := "Emitted in VS Code when a running request is cancelled, e.g. when the document state has changed."
  },
  .request {
    method := "initialize"
    direction := .clientToServer
    kinds := #[
      .standardViolation "The Lean language server currently ignores almost all standard client capabilities and expects clients to be sufficiently fully-featured.",
      .standardViolation "The `InitializeParams.rootUri?` field is not used by the language server - it instead uses the cwd of the language server process.",
      .extendedParameterType #[``InitializeParams.initializationOptions?, ``InitializeParams.capabilities, ``ClientCapabilities.lean?]
    ]
    parameterType := InitializeParams
    responseType := InitializeResult
    description := "Emitted when the language server is being initialized. The server is only started once an `initialized` notification is emitted after the `initialize` request."
  },
  .notification {
    method := "initialized"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := InitializedParams
    description := "Emitted after a response to the `initialize` request to start the server."
  },
  .request {
    method := "shutdown"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := Option Empty
    responseType := Option Empty
    description := "Emitted when the language server is being asked to shut down and deliver responses for all pending requests."
  },
  .notification {
    method := "exit"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := Option Empty
    description := "Emitted once the language server should shut down after a `shutdown` request."
  },
  .request {
    method := "client/registerCapability"
    direction := .serverToClient
    kinds := #[.standard]
    parameterType := NestedType #[Option RegistrationParams, DidChangeWatchedFilesRegistrationOptions]
    responseType := Option Empty
    description := "Emitted by the language server after receiving the `initialized` notification to register file watchers for `.lean` and `.ilean` files using the `workspace/didChangeWatchedFiles` registration."
  },
  .notification {
    method := "textDocument/didOpen"
    direction := .clientToServer
    kinds := #[.extendedParameterType #[``LeanDidOpenTextDocumentParams.dependencyBuildMode?]]
    parameterType := LeanDidOpenTextDocumentParams
    description := "Emitted in VS Code when a text document is opened. VS Code may sometimes emit this notification for files that were not opened in an editor."
  },
  .notification {
    method := "textDocument/didClose"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DidCloseTextDocumentParams
    description := "Emitted in VS Code when a text document is closed. VS Code may sometimes emit this notification for files that were not opened in an editor."
  },
  .notification {
    method := "textDocument/didChange"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DidChangeTextDocumentParams
    description := "Emitted in VS Code when a text document is edited."
  },
  .notification {
    method := "textDocument/didSave"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DidSaveTextDocumentParams
    description := "Emitted in VS Code when a text document is saved."
  },
  .notification {
    method := "workspace/didChangeWatchedFiles"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DidChangeWatchedFilesParams
    description := "Emitted in VS Code when one of the files that the language server registered a file watcher for changes."
  },
  .notification {
    method := "textDocument/publishDiagnostics"
    direction := .serverToClient
    kinds := #[.extendedParameterType #[``PublishDiagnosticsParams.diagnostics, ``DiagnosticWith.fullRange?, ``DiagnosticWith.isSilent?, ``DiagnosticWith.leanTags?]]
    parameterType := PublishDiagnosticsParams
    description := "Emitted by the language server whenever a new set of diagnostics becomes available for a file. Unlike most language servers, the Lean language server emits this notification incrementally while processing the file, not only when the full file has been processed."
  },
  .notification {
    method := "$/lean/fileProgress"
    direction := .serverToClient
    kinds := #[.leanSpecificMethod]
    parameterType := LeanFileProgressParams
    description := "Emitted by the language server whenever the elaboration progress of a file changes."
  },
  .request {
    method := "textDocument/completion"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CompletionParams
    responseType := CompletionList
    description := "Emitted in VS Code when auto-completion is triggered, e.g. automatically while typing or after hitting Ctrl+Space."
  },
  .request {
    method := "completionItem/resolve"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CompletionItem
    responseType := CompletionItem
    description := "Emitted in VS Code when an auto-completion entry is selected."
  },
  .request {
    method := "textDocument/codeAction"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CodeActionParams
    responseType := Array CodeAction
    description := "Emitted in VS Code when code actions are triggered, e.g. automatically while typing, moving the text cursor or when hovering over a diagnostic."
  },
  .request {
    method := "codeAction/resolve"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CodeAction
    responseType := CodeAction
    description := "Emitted in VS Code when a code action in the light bulb menu is selected."
  },
  .request {
    method := "textDocument/signatureHelp"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := SignatureHelpParams
    responseType := Option SignatureHelp
    description := "Emitted in VS Code when the signature help is triggered, e.g. automatically while typing or after hitting Ctrl+Shift+Space."
  },
  .request {
    method := "textDocument/hover"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := HoverParams
    responseType := Option Hover
    description := "Emitted in VS Code when hovering over an identifier in the editor."
  },
  .request {
    method := "textDocument/documentHighlight"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DocumentHighlightParams
    responseType := DocumentHighlightResult
    description := "Emitted in VS Code when the text cursor is on an identifier."
  },
  .request {
    method := "textDocument/documentSymbol"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DocumentSymbolParams
    responseType := DocumentSymbolResult
    description := "Emitted in VS Code when a file is first opened or when it is changed."
  },
  .request {
    method := "textDocument/foldingRange"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := FoldingRangeParams
    responseType := Array FoldingRange
    description := "Emitted in VS Code when a file is first opened or when it is changed."
  },
  .request {
    method := "textDocument/documentColor"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DocumentColorParams
    responseType := Array ColorInformation
    description := "Emitted in VS Code when a file is first opened or when it is changed. The language server defines this handler to override the default document color handler of VS Code with an empty one."
  },
  .request {
    method := "textDocument/semanticTokens/range"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := SemanticTokensRangeParams
    responseType := SemanticTokens
    description := "Emitted in VS Code when a file is changed."
  },
  .request {
    method := "textDocument/semanticTokens/full"
    direction := .clientToServer
    kinds := #[.standardViolation "Instead of reporting the full semantic tokens for the full file as specified by LSP, the Lean language server will only report the semantic tokens for the part of the file that has been processed so far. If the response is incomplete, the language server periodically emits `workspace/semanticTokens/refresh` to request another `textDocument/semanticTokens/full` request from the client. This process is repeated until the file has been fully processed and all semantic tokens have been reported. We use this trick to stream semantic tokens to VS Code, despite the fact that VS Code does not support result streaming."]
    parameterType := SemanticTokensParams
    responseType := SemanticTokens
    description := "Emitted in VS Code when a file is first opened, when it is changed or when VS Code receives a `workspace/semanticTokens/refresh` request from the server."
  },
  .request {
    method := "workspace/semanticTokens/refresh"
    direction := .serverToClient
    kinds := #[.standard]
    parameterType := Option Empty
    responseType := Option Empty
    description := "Emitted by the language server to request another `textDocument/semanticTokens/full` request from the client."
  },
  .request {
    method := "textDocument/inlayHint"
    direction := .clientToServer
    kinds := #[.standardViolation "Instead of reporting the full inlay hints for the full file as specified by LSP, the Lean language server will only report the inlay hints for the part of the file that has been processed so far. If the response is incomplete, the language server periodically emits `workspace/inlayHint/refresh` to request another `textDocument/inlayHint` request from the client. This process is repeated until the file has been fully processed and all inlay hints have been reported. We use this trick to stream inlay hints to VS Code, despite the fact that VS Code does not support result streaming."]
    parameterType := InlayHintParams
    responseType := Array InlayHint
    description := "Emitted in VS Code when a file is first opened, when it is changed or when VS Code receives a `workspace/inlayHint/refresh` request from the server."
  },
  .request {
    method := "workspace/inlayHint/refresh"
    direction := .serverToClient
    kinds := #[.standard]
    parameterType := Option Empty
    responseType := Option Empty
    description := "Emitted by the language server to request another `textDocument/inlayHint` request from the client."
  },
  .request {
    method := "textDocument/definition"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DefinitionParams
    responseType := Array LocationLink
    description := "Emitted in VS Code when clicking 'Go to Definition' in the context menu or using Ctrl+Click."
  },
  .request {
    method := "textDocument/declaration"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DefinitionParams
    responseType := Array LocationLink
    description := "Emitted in VS Code when clicking 'Go to Declaration' in the context menu."
  },
  .request {
    method := "textDocument/typeDefinition"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := DefinitionParams
    responseType := Array LocationLink
    description := "Emitted in VS Code when clicking 'Go to Type Definition' in the context menu."
  },
  .request {
    method := "textDocument/references"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := ReferenceParams
    responseType := Array Location
    description := "Emitted in VS Code when clicking 'Find All References' or 'Go to References' in the context menu."
  },
  .request {
    method := "textDocument/prepareCallHierarchy"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CallHierarchyPrepareParams
    responseType := Array CallHierarchyItem
    description := "Emitted in VS Code when clicking 'Show Call Hierarchy' in the context menu."
  },
  .request {
    method := "callHierarchy/incomingCalls"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CallHierarchyIncomingCallsParams
    responseType := Array CallHierarchyIncomingCall
    description := "Emitted in VS Code when expanding a node in the call hierarchy in 'incoming calls' mode."
  },
  .request {
    method := "callHierarchy/outgoingCalls"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := CallHierarchyOutgoingCallsParams
    responseType := Array CallHierarchyOutgoingCall
    description := "Emitted in VS Code when expanding a node in the call hierarchy in 'outgoing calls' mode."
  },
  .request {
    method := "$/lean/prepareModuleHierarchy"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := LeanPrepareModuleHierarchyParams
    responseType := Option LeanModule
    description := "Emitted in VS Code when clicking 'Show Module Hierarchy' or 'Show Inverse Module Hierarchy' in the context menu."
  },
  .request {
    method := "$/lean/moduleHierarchy/imports"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := LeanModuleHierarchyImportsParams
    responseType := Array LeanImport
    description := "Emitted in VS Code when expanding a node in the module hierarchy."
  },
  .request {
    method := "$/lean/moduleHierarchy/importedBy"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := LeanModuleHierarchyImportedByParams
    responseType := Array LeanImport
    description := "Emitted in VS Code when expanding a node in the inverse module hierarchy."
  },
  .request {
    method := "textDocument/prepareRename"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := PrepareRenameParams
    responseType := Option Range
    description := "Emitted in VS Code when clicking 'Rename Symbol' in the context menu."
  },
  .request {
    method := "textDocument/rename"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := RenameParams
    responseType := WorkspaceEdit
    description := "Emitted in VS Code when entering an identifier after clicking 'Rename Symbol' in the context menu."
  },
  .request {
    method := "workspace/symbol"
    direction := .clientToServer
    kinds := #[.standard]
    parameterType := WorkspaceSymbolParams
    responseType := Array SymbolInformation
    description := "Emitted in VS Code when opening the command prompt and entering a `#` prefix with a query after it."
  },
  .request {
    method := "$/lean/plainGoal"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := PlainGoalParams
    responseType := Option PlainGoal
    description := "Not used in VS Code. Emitted in editors that do not support an interactive InfoView (e.g. Emacs) and interactive tests."
  },
  .request {
    method := "$/lean/plainTermGoal"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := PlainTermGoalParams
    responseType := Option PlainTermGoal
    description := "Not used in VS Code. Emitted in editors that do not support an interactive InfoView (e.g. Emacs) and interactive tests."
  },
  .request {
    method := "textDocument/waitForDiagnostics"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := WaitForDiagnosticsParams
    responseType := WaitForDiagnostics
    description := "Not used in the editor. Emitted in interactive tests to wait for all diagnostics up to a given point."
  },
  .request {
    method := "$/lean/waitForILeans"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := WaitForILeansParams
    responseType := WaitForILeans
    description := "Not used in the editor. Emitted in interactive tests to wait for all .ileans in the project and the .ilean of the given file to be loaded."
  },
  .request {
    method := "$/lean/rpc/connect"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := RpcConnectParams
    responseType := RpcConnected
    description := "Emitted in VS Code when an RPC session for InfoView interactivity is initially set up."
  },
  .notification {
    method := "$/lean/rpc/release"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := RpcReleaseParams
    description := "Emitted in VS Code when an RPC object in the server (the lifecycle of which is managed by the client) is freed by the client."
  },
  .notification {
    method := "$/lean/rpc/keepAlive"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := RpcKeepAliveParams
    description := "Emitted periodically in VS Code to signal that the RPC client has not disconnected yet to keep the RPC session alive."
  },
  .request {
    method := "$/lean/rpc/call"
    direction := .clientToServer
    kinds := #[.leanSpecificMethod]
    parameterType := RpcCallParams
    responseType := Json
    description := "Emitted in VS Code when an RPC method is called. `RpcCallParams.method` and `RpcCallParams.params` can be any of the builtin `.rpcRequest`s described in this overview or any custom RPC methods tagged with `@[server_rpc_method]` that can be set up for use in the widget system."
  },
  .rpcRequest {
    method := `Lean.Widget.getInteractiveDiagnostics
    parameterType := GetInteractiveDiagnosticsParams
    responseType := Array InteractiveDiagnostic
    description := "Emitted in VS Code when the text cursor is moved, the set of diagnostics at the cursor position changes or the file starts or finishes processing."
  },
  .rpcRequest {
    method := `Lean.Widget.getInteractiveGoals
    parameterType := Lsp.PlainGoalParams
    responseType := Option InteractiveGoals
    description := "Emitted in VS Code when the text cursor is moved, the set of diagnostics at the cursor position changes or the file starts or finishes processing."
  },
  .rpcRequest {
    method := `Lean.Widget.getInteractiveTermGoal
    parameterType := Lsp.PlainTermGoalParams
    responseType := Option InteractiveTermGoal
    description := "Emitted in VS Code when the text cursor is moved, the set of diagnostics at the cursor position changes or the file starts or finishes processing."
  },
  .rpcRequest {
    method := `Lean.Widget.getWidgets
    parameterType := Position
    responseType := GetWidgetsResponse
    description := "Emitted in VS Code when the text cursor is moved, the set of diagnostics at the cursor position changes or the file starts or finishes processing."
  },
  .rpcRequest {
    method := `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    parameterType := WithRpcRef Elab.InfoWithCtx
    responseType := InfoPopup
    description := "Emitted in VS Code when hovering over terms in the InfoView."
  },
  .rpcRequest {
    method := `Lean.Widget.getGoToLocation
    parameterType := GetGoToLocationParams
    responseType := Array Lsp.LocationLink
    description := "Emitted in VS Code when clicking 'Go to Definition' in the context menu of the InfoView or using Ctrl+Click in the InfoView."
  },
  .rpcRequest {
    method := `Lean.Widget.lazyTraceChildrenToInteractive
    parameterType := WithRpcRef LazyTraceChildren
    responseType := Array InteractiveMessage
    description := "Emitted in VS Code when unfolding a lazy trace message in the InfoView."
  },
  .rpcRequest {
    method := `Lean.Widget.highlightMatches
    parameterType := HighlightMatchesParams
    responseType := HighlightedInteractiveMessage
    description := "Emitted in VS Code when using the trace search in the InfoView."
  },
  .rpcRequest {
    method := `Lean.Widget.getWidgetSource
    parameterType := GetWidgetSourceParams
    responseType := WidgetSource
    description := "Emitted in VS Code when a widget is imported from another widget."
  },
  .rpcRequest {
    method := `Lean.Widget.InteractiveDiagnostics.msgToInteractive
    parameterType := MsgToInteractive
    responseType := InteractiveMessage
    description := "Emitted in VS Code in some widgets to convert non-interactive messages to interactive ones."
  },
]
