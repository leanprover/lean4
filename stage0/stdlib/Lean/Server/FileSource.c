// Lean compiler output
// Module: Lean.Server.FileSource
// Imports: public import Lean.Data.Lsp
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
static lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0;
lean_object* l_Lean_Json_getArrVal_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0;
static lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier;
static lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams;
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3;
static lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionItem;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedFileIdent_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedFileIdent;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_uri_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorIdx(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0;
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instToStringFileIdent___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceHoverParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams;
static lean_object* l_Lean_Lsp_instFileSourceReferenceParams___closed__0;
static lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_mod_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDefinitionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringFileIdent;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit;
static lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_mod_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDeclarationParams;
static lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringFileIdent___lam__0(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams;
static lean_object* l_Lean_Lsp_instFileSourceLocation___closed__0;
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1;
static lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Lsp_instInhabitedFileIdent_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceCompletionItem___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_uri_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(lean_object*);
static lean_object* l_Lean_Lsp_instInhabitedFileIdent_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams;
static lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileIdent_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_FileIdent_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_FileIdent_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_uri_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_FileIdent_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_uri_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lsp_FileIdent_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_mod_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_FileIdent_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileIdent_mod_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lsp_FileIdent_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedFileIdent_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedFileIdent_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_instInhabitedFileIdent_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedFileIdent_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedFileIdent_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedFileIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedFileIdent_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringFileIdent___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToStringFileIdent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instToStringFileIdent___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToStringFileIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToStringFileIdent___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceLocation___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceLocation___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceLocation___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceLocation___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentEdit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentItem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCompletionParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceHoverParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDeclarationParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDefinitionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceTypeDefinitionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceReferenceParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceReferenceParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceReferenceParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceReferenceParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentHighlightParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSemanticTokensParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceFoldingRangeParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourcePlainGoalParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourcePlainTermGoalParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcConnectParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcCallParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcCallParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceRpcCallParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcReleaseParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCodeActionParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCodeActionParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCodeActionParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceInlayHintParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceInlayHintParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceInlayHintParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceSignatureHelpParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceDocumentColorParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instInhabitedFileIdent_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Name_fromJson_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.FileSource", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Lsp.CompletionItem.getFileSource!", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected completion item data: ", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no data param on completion item ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 6);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
switch (lean_obj_tag(x_11)) {
case 5:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2;
x_13 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_2 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
case 4:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Json_getArrVal_x3f(x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_2 = x_20;
goto block_9;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Name_fromJson_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_2 = x_23;
goto block_9;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3;
x_28 = lean_unsigned_to_nat(80u);
x_29 = l_Lean_Json_pretty(x_11, x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_2 = x_30;
goto block_9;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_1);
x_32 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4;
x_33 = lean_string_append(x_32, x_31);
lean_dec_ref(x_31);
x_2 = x_33;
goto block_9;
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0;
x_4 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1;
x_5 = lean_unsigned_to_nat(154u);
x_6 = lean_unsigned_to_nat(22u);
x_7 = l_mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_2);
lean_dec_ref(x_2);
x_8 = l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionItem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_getFileSource_x21), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionItem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionItem___closed__0;
return x_1;
}
}
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileSource(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedFileIdent_default___closed__0 = _init_l_Lean_Lsp_instInhabitedFileIdent_default___closed__0();
lean_mark_persistent(l_Lean_Lsp_instInhabitedFileIdent_default___closed__0);
l_Lean_Lsp_instInhabitedFileIdent_default___closed__1 = _init_l_Lean_Lsp_instInhabitedFileIdent_default___closed__1();
lean_mark_persistent(l_Lean_Lsp_instInhabitedFileIdent_default___closed__1);
l_Lean_Lsp_instInhabitedFileIdent_default = _init_l_Lean_Lsp_instInhabitedFileIdent_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedFileIdent_default);
l_Lean_Lsp_instInhabitedFileIdent = _init_l_Lean_Lsp_instInhabitedFileIdent();
lean_mark_persistent(l_Lean_Lsp_instInhabitedFileIdent);
l_Lean_Lsp_instToStringFileIdent___closed__0 = _init_l_Lean_Lsp_instToStringFileIdent___closed__0();
lean_mark_persistent(l_Lean_Lsp_instToStringFileIdent___closed__0);
l_Lean_Lsp_instToStringFileIdent = _init_l_Lean_Lsp_instToStringFileIdent();
lean_mark_persistent(l_Lean_Lsp_instToStringFileIdent);
l_Lean_Lsp_instFileSourceLocation___closed__0 = _init_l_Lean_Lsp_instFileSourceLocation___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceLocation___closed__0);
l_Lean_Lsp_instFileSourceLocation = _init_l_Lean_Lsp_instFileSourceLocation();
lean_mark_persistent(l_Lean_Lsp_instFileSourceLocation);
l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0 = _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0);
l_Lean_Lsp_instFileSourceTextDocumentIdentifier = _init_l_Lean_Lsp_instFileSourceTextDocumentIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentIdentifier);
l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0 = _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0);
l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier = _init_l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier);
l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0 = _init_l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0);
l_Lean_Lsp_instFileSourceTextDocumentEdit = _init_l_Lean_Lsp_instFileSourceTextDocumentEdit();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentEdit);
l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0 = _init_l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0);
l_Lean_Lsp_instFileSourceTextDocumentItem = _init_l_Lean_Lsp_instFileSourceTextDocumentItem();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentItem);
l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0 = _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0);
l_Lean_Lsp_instFileSourceTextDocumentPositionParams = _init_l_Lean_Lsp_instFileSourceTextDocumentPositionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTextDocumentPositionParams);
l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0);
l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams);
l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0);
l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams);
l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0);
l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams);
l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0);
l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams = _init_l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams);
l_Lean_Lsp_instFileSourceCompletionParams___closed__0 = _init_l_Lean_Lsp_instFileSourceCompletionParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionParams___closed__0);
l_Lean_Lsp_instFileSourceCompletionParams = _init_l_Lean_Lsp_instFileSourceCompletionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionParams);
l_Lean_Lsp_instFileSourceHoverParams = _init_l_Lean_Lsp_instFileSourceHoverParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceHoverParams);
l_Lean_Lsp_instFileSourceDeclarationParams = _init_l_Lean_Lsp_instFileSourceDeclarationParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDeclarationParams);
l_Lean_Lsp_instFileSourceDefinitionParams = _init_l_Lean_Lsp_instFileSourceDefinitionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDefinitionParams);
l_Lean_Lsp_instFileSourceTypeDefinitionParams = _init_l_Lean_Lsp_instFileSourceTypeDefinitionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceTypeDefinitionParams);
l_Lean_Lsp_instFileSourceReferenceParams___closed__0 = _init_l_Lean_Lsp_instFileSourceReferenceParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceReferenceParams___closed__0);
l_Lean_Lsp_instFileSourceReferenceParams = _init_l_Lean_Lsp_instFileSourceReferenceParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceReferenceParams);
l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0 = _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0);
l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams = _init_l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams);
l_Lean_Lsp_instFileSourceDocumentHighlightParams = _init_l_Lean_Lsp_instFileSourceDocumentHighlightParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentHighlightParams);
l_Lean_Lsp_instFileSourceDocumentSymbolParams = _init_l_Lean_Lsp_instFileSourceDocumentSymbolParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentSymbolParams);
l_Lean_Lsp_instFileSourceSemanticTokensParams = _init_l_Lean_Lsp_instFileSourceSemanticTokensParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSemanticTokensParams);
l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0 = _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0);
l_Lean_Lsp_instFileSourceSemanticTokensRangeParams = _init_l_Lean_Lsp_instFileSourceSemanticTokensRangeParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams);
l_Lean_Lsp_instFileSourceFoldingRangeParams = _init_l_Lean_Lsp_instFileSourceFoldingRangeParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceFoldingRangeParams);
l_Lean_Lsp_instFileSourcePlainGoalParams = _init_l_Lean_Lsp_instFileSourcePlainGoalParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourcePlainGoalParams);
l_Lean_Lsp_instFileSourcePlainTermGoalParams = _init_l_Lean_Lsp_instFileSourcePlainTermGoalParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourcePlainTermGoalParams);
l_Lean_Lsp_instFileSourceRpcConnectParams = _init_l_Lean_Lsp_instFileSourceRpcConnectParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcConnectParams);
l_Lean_Lsp_instFileSourceRpcCallParams___closed__0 = _init_l_Lean_Lsp_instFileSourceRpcCallParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcCallParams___closed__0);
l_Lean_Lsp_instFileSourceRpcCallParams = _init_l_Lean_Lsp_instFileSourceRpcCallParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcCallParams);
l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0 = _init_l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0);
l_Lean_Lsp_instFileSourceRpcReleaseParams = _init_l_Lean_Lsp_instFileSourceRpcReleaseParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcReleaseParams);
l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0 = _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0);
l_Lean_Lsp_instFileSourceRpcKeepAliveParams = _init_l_Lean_Lsp_instFileSourceRpcKeepAliveParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceRpcKeepAliveParams);
l_Lean_Lsp_instFileSourceCodeActionParams___closed__0 = _init_l_Lean_Lsp_instFileSourceCodeActionParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCodeActionParams___closed__0);
l_Lean_Lsp_instFileSourceCodeActionParams = _init_l_Lean_Lsp_instFileSourceCodeActionParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCodeActionParams);
l_Lean_Lsp_instFileSourceInlayHintParams___closed__0 = _init_l_Lean_Lsp_instFileSourceInlayHintParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceInlayHintParams___closed__0);
l_Lean_Lsp_instFileSourceInlayHintParams = _init_l_Lean_Lsp_instFileSourceInlayHintParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceInlayHintParams);
l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0 = _init_l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0);
l_Lean_Lsp_instFileSourceSignatureHelpParams = _init_l_Lean_Lsp_instFileSourceSignatureHelpParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceSignatureHelpParams);
l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0 = _init_l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0);
l_Lean_Lsp_instFileSourceDocumentColorParams = _init_l_Lean_Lsp_instFileSourceDocumentColorParams();
lean_mark_persistent(l_Lean_Lsp_instFileSourceDocumentColorParams);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4);
l_Lean_Lsp_instFileSourceCompletionItem___closed__0 = _init_l_Lean_Lsp_instFileSourceCompletionItem___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionItem___closed__0);
l_Lean_Lsp_instFileSourceCompletionItem = _init_l_Lean_Lsp_instFileSourceCompletionItem();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionItem);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
