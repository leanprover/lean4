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
static lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams;
static lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams;
static lean_object* l_Lean_Lsp_instFileSourceHoverParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceLocation() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceLocation___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceLocation___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentEdit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentItem() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCompletionParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceHoverParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceHoverParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceHoverParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDeclarationParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceHoverParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDefinitionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceHoverParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTypeDefinitionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceHoverParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceReferenceParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceReferenceParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentHighlightParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceHoverParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSemanticTokensParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceFoldingRangeParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourcePlainGoalParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourcePlainTermGoalParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcConnectParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcCallParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcReleaseParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCodeActionParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceInlayHintParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSignatureHelpParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(x_1);
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
l_Lean_Lsp_instFileSourceLocation = _init_l_Lean_Lsp_instFileSourceLocation();
lean_mark_persistent(l_Lean_Lsp_instFileSourceLocation);
l_Lean_Lsp_instFileSourceTextDocumentIdentifier = _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentIdentifier);
l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier = _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier);
l_Lean_Lsp_instFileSourceTextDocumentEdit = _init_l_Lean_Lsp_instFileSourceTextDocumentEdit();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentEdit);
l_Lean_Lsp_instFileSourceTextDocumentItem = _init_l_Lean_Lsp_instFileSourceTextDocumentItem();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentItem);
l_Lean_Lsp_instFileSourceTextDocumentPositionParams = _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentPositionParams);
l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams);
l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams);
l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams);
l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams);
l_Lean_Lsp_instFileSourceCompletionParams = _init_l_Lean_Lsp_instFileSourceCompletionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionParams);
l_Lean_Lsp_instFileSourceHoverParams___closed__0 = _init_l_Lean_Lsp_instFileSourceHoverParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceHoverParams___closed__0);
l_Lean_Lsp_instFileSourceHoverParams = _init_l_Lean_Lsp_instFileSourceHoverParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceHoverParams);
l_Lean_Lsp_instFileSourceDeclarationParams = _init_l_Lean_Lsp_instFileSourceDeclarationParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDeclarationParams);
l_Lean_Lsp_instFileSourceDefinitionParams = _init_l_Lean_Lsp_instFileSourceDefinitionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDefinitionParams);
l_Lean_Lsp_instFileSourceTypeDefinitionParams = _init_l_Lean_Lsp_instFileSourceTypeDefinitionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTypeDefinitionParams);
l_Lean_Lsp_instFileSourceReferenceParams = _init_l_Lean_Lsp_instFileSourceReferenceParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceReferenceParams);
l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams = _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams);
l_Lean_Lsp_instFileSourceDocumentHighlightParams = _init_l_Lean_Lsp_instFileSourceDocumentHighlightParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentHighlightParams);
l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentSymbolParams___closed__0);
l_Lean_Lsp_instFileSourceDocumentSymbolParams = _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentSymbolParams);
l_Lean_Lsp_instFileSourceSemanticTokensParams = _init_l_Lean_Lsp_instFileSourceSemanticTokensParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSemanticTokensParams);
l_Lean_Lsp_instFileSourceSemanticTokensRangeParams = _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams);
l_Lean_Lsp_instFileSourceFoldingRangeParams = _init_l_Lean_Lsp_instFileSourceFoldingRangeParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceFoldingRangeParams);
l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0 = _init_l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourcePlainGoalParams___closed__0);
l_Lean_Lsp_instFileSourcePlainGoalParams = _init_l_Lean_Lsp_instFileSourcePlainGoalParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourcePlainGoalParams);
l_Lean_Lsp_instFileSourcePlainTermGoalParams = _init_l_Lean_Lsp_instFileSourcePlainTermGoalParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourcePlainTermGoalParams);
l_Lean_Lsp_instFileSourceRpcConnectParams = _init_l_Lean_Lsp_instFileSourceRpcConnectParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcConnectParams);
l_Lean_Lsp_instFileSourceRpcCallParams = _init_l_Lean_Lsp_instFileSourceRpcCallParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcCallParams);
l_Lean_Lsp_instFileSourceRpcReleaseParams = _init_l_Lean_Lsp_instFileSourceRpcReleaseParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcReleaseParams);
l_Lean_Lsp_instFileSourceRpcKeepAliveParams = _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcKeepAliveParams);
l_Lean_Lsp_instFileSourceCodeActionParams = _init_l_Lean_Lsp_instFileSourceCodeActionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCodeActionParams);
l_Lean_Lsp_instFileSourceInlayHintParams = _init_l_Lean_Lsp_instFileSourceInlayHintParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceInlayHintParams);
l_Lean_Lsp_instFileSourceSignatureHelpParams = _init_l_Lean_Lsp_instFileSourceSignatureHelpParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSignatureHelpParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
