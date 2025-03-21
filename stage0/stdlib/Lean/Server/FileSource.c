// Lean compiler output
// Module: Lean.Server.FileSource
// Imports: Lean.Data.Lsp
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceLocation(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentIdentifier(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentEdit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentItem(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCompletionParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceHoverParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDeclarationParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDefinitionParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTypeDefinitionParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceReferenceParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDocumentHighlightParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDocumentSymbolParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSemanticTokensParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceFoldingRangeParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourcePlainGoalParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourcePlainTermGoalParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcConnectParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcCallParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcReleaseParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcKeepAliveParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCodeActionParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceInlayHintParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileSource(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
