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
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArrVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceLocation___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceLocation___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceLocation = (const lean_object*)&l_Lean_Lsp_instFileSourceLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceCompletionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceCompletionParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceHoverParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDeclarationParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDefinitionParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceTypeDefinitionParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceReferenceParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceReferenceParams = (const lean_object*)&l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDocumentHighlightParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDocumentSymbolParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceSemanticTokensParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams = (const lean_object*)&l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceFoldingRangeParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourcePlainGoalParams = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourcePlainTermGoalParams = (const lean_object*)&l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceRpcConnectParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceRpcCallParams = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams = (const lean_object*)&l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceCodeActionParams = (const lean_object*)&l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceInlayHintParams = (const lean_object*)&l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams = (const lean_object*)&l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams = (const lean_object*)&l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value;
static const lean_string_object l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Server.FileSource"};
static const lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0 = (const lean_object*)&l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Lsp.CompletionItem.getFileSource!"};
static const lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1 = (const lean_object*)&l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2 = (const lean_object*)&l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected completion item data: "};
static const lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3 = (const lean_object*)&l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3_value;
static const lean_string_object l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "no data param on completion item "};
static const lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4 = (const lean_object*)&l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CompletionItem_getFileSource_x21, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFileSourceCompletionItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFileSourceCompletionItem = (const lean_object*)&l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0(lean_object* v_l_1_){
_start:
{
lean_object* v_uri_2_; 
v_uri_2_ = lean_ctor_get(v_l_1_, 0);
lean_inc_ref(v_uri_2_);
return v_uri_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(lean_object* v_l_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Lsp_instFileSourceLocation___lam__0(v_l_3_);
lean_dec_ref(v_l_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(lean_object* v_i_7_){
_start:
{
lean_inc_ref(v_i_7_);
return v_i_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed(lean_object* v_i_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(v_i_8_);
lean_dec_ref(v_i_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(lean_object* v_i_12_){
_start:
{
lean_object* v_uri_13_; 
v_uri_13_ = lean_ctor_get(v_i_12_, 0);
lean_inc_ref(v_uri_13_);
return v_uri_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(lean_object* v_i_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(v_i_14_);
lean_dec_ref(v_i_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(lean_object* v_e_18_){
_start:
{
lean_object* v_textDocument_19_; lean_object* v_uri_20_; 
v_textDocument_19_ = lean_ctor_get(v_e_18_, 0);
v_uri_20_ = lean_ctor_get(v_textDocument_19_, 0);
lean_inc_ref(v_uri_20_);
return v_uri_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(lean_object* v_e_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(v_e_21_);
lean_dec_ref(v_e_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(lean_object* v_i_25_){
_start:
{
lean_object* v_uri_26_; 
v_uri_26_ = lean_ctor_get(v_i_25_, 0);
lean_inc_ref(v_uri_26_);
return v_uri_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(lean_object* v_i_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(v_i_27_);
lean_dec_ref(v_i_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(lean_object* v_p_31_){
_start:
{
lean_object* v_textDocument_32_; 
v_textDocument_32_ = lean_ctor_get(v_p_31_, 0);
lean_inc_ref(v_textDocument_32_);
return v_textDocument_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(lean_object* v_p_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(v_p_33_);
lean_dec_ref(v_p_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(lean_object* v_p_37_){
_start:
{
lean_object* v_uri_38_; 
v_uri_38_ = lean_ctor_get(v_p_37_, 0);
lean_inc_ref(v_uri_38_);
return v_uri_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(lean_object* v_p_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(v_p_39_);
lean_dec_ref(v_p_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(lean_object* v_p_43_){
_start:
{
lean_object* v_textDocument_44_; lean_object* v_uri_45_; 
v_textDocument_44_ = lean_ctor_get(v_p_43_, 0);
v_uri_45_ = lean_ctor_get(v_textDocument_44_, 0);
lean_inc_ref(v_uri_45_);
return v_uri_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(lean_object* v_p_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(v_p_46_);
lean_dec_ref(v_p_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(lean_object* v_p_50_){
_start:
{
lean_object* v_textDocument_51_; 
v_textDocument_51_ = lean_ctor_get(v_p_50_, 0);
lean_inc_ref(v_textDocument_51_);
return v_textDocument_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(lean_object* v_p_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(v_p_52_);
lean_dec_ref(v_p_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(lean_object* v_p_56_){
_start:
{
lean_inc_ref(v_p_56_);
return v_p_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed(lean_object* v_p_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(v_p_57_);
lean_dec_ref(v_p_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0(lean_object* v_h_61_){
_start:
{
lean_object* v_textDocument_62_; 
v_textDocument_62_ = lean_ctor_get(v_h_61_, 0);
lean_inc_ref(v_textDocument_62_);
return v_textDocument_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(lean_object* v_h_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Lsp_instFileSourceCompletionParams___lam__0(v_h_63_);
lean_dec_ref(v_h_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0(lean_object* v_h_71_){
_start:
{
lean_object* v_toTextDocumentPositionParams_72_; lean_object* v_textDocument_73_; 
v_toTextDocumentPositionParams_72_ = lean_ctor_get(v_h_71_, 0);
v_textDocument_73_ = lean_ctor_get(v_toTextDocumentPositionParams_72_, 0);
lean_inc_ref(v_textDocument_73_);
return v_textDocument_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(lean_object* v_h_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Lsp_instFileSourceReferenceParams___lam__0(v_h_74_);
lean_dec_ref(v_h_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(lean_object* v_p_78_){
_start:
{
lean_object* v_uri_79_; 
v_uri_79_ = lean_ctor_get(v_p_78_, 0);
lean_inc_ref(v_uri_79_);
return v_uri_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(lean_object* v_p_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(v_p_80_);
lean_dec_ref(v_p_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(lean_object* v_p_87_){
_start:
{
lean_object* v_textDocument_88_; 
v_textDocument_88_ = lean_ctor_get(v_p_87_, 0);
lean_inc_ref(v_textDocument_88_);
return v_textDocument_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(lean_object* v_p_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(v_p_89_);
lean_dec_ref(v_p_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(lean_object* v_p_97_){
_start:
{
lean_object* v_toTextDocumentPositionParams_98_; lean_object* v_textDocument_99_; 
v_toTextDocumentPositionParams_98_ = lean_ctor_get(v_p_97_, 0);
v_textDocument_99_ = lean_ctor_get(v_toTextDocumentPositionParams_98_, 0);
lean_inc_ref(v_textDocument_99_);
return v_textDocument_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(lean_object* v_p_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(v_p_100_);
lean_dec_ref(v_p_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(lean_object* v_p_104_){
_start:
{
lean_object* v_uri_105_; 
v_uri_105_ = lean_ctor_get(v_p_104_, 0);
lean_inc_ref(v_uri_105_);
return v_uri_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(lean_object* v_p_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(v_p_106_);
lean_dec_ref(v_p_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(lean_object* v_p_110_){
_start:
{
lean_object* v_uri_111_; 
v_uri_111_ = lean_ctor_get(v_p_110_, 0);
lean_inc_ref(v_uri_111_);
return v_uri_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(lean_object* v_p_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(v_p_112_);
lean_dec_ref(v_p_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(lean_object* v_p_116_){
_start:
{
lean_object* v_textDocument_117_; 
v_textDocument_117_ = lean_ctor_get(v_p_116_, 2);
lean_inc_ref(v_textDocument_117_);
return v_textDocument_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(lean_object* v_p_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(v_p_118_);
lean_dec_ref(v_p_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(lean_object* v_p_122_){
_start:
{
lean_object* v_textDocument_123_; 
v_textDocument_123_ = lean_ctor_get(v_p_122_, 1);
lean_inc_ref(v_textDocument_123_);
return v_textDocument_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(lean_object* v_p_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(v_p_124_);
lean_dec_ref(v_p_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(lean_object* v_p_128_){
_start:
{
lean_object* v_toTextDocumentPositionParams_129_; lean_object* v_textDocument_130_; 
v_toTextDocumentPositionParams_129_ = lean_ctor_get(v_p_128_, 0);
v_textDocument_130_ = lean_ctor_get(v_toTextDocumentPositionParams_129_, 0);
lean_inc_ref(v_textDocument_130_);
return v_textDocument_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(lean_object* v_p_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(v_p_131_);
lean_dec_ref(v_p_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(lean_object* v_p_135_){
_start:
{
lean_object* v_textDocument_136_; 
v_textDocument_136_ = lean_ctor_get(v_p_135_, 2);
lean_inc_ref(v_textDocument_136_);
return v_textDocument_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed(lean_object* v_p_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(v_p_137_);
lean_dec_ref(v_p_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object* v_msg_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0));
v___x_144_ = lean_panic_fn(v___x_143_, v_msg_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(lean_object* v_j_145_, lean_object* v_k_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = l_Lean_Json_getObjValD(v_j_145_, v_k_146_);
v___x_148_ = l_Lean_Json_getStr_x3f(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1___boxed(lean_object* v_j_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(v_j_149_, v_k_150_);
lean_dec_ref(v_k_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object* v_item_157_){
_start:
{
lean_object* v_a_159_; lean_object* v___y_167_; lean_object* v_data_x3f_170_; 
v_data_x3f_170_ = lean_ctor_get(v_item_157_, 6);
if (lean_obj_tag(v_data_x3f_170_) == 1)
{
lean_object* v_val_171_; 
lean_inc_ref(v_data_x3f_170_);
lean_dec_ref(v_item_157_);
v_val_171_ = lean_ctor_get(v_data_x3f_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref(v_data_x3f_170_);
switch(lean_obj_tag(v_val_171_))
{
case 5:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2));
v___x_173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(v_val_171_, v___x_172_);
v___y_167_ = v___x_173_;
goto v___jp_166_;
}
case 4:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Lean_Json_getArrVal_x3f(v_val_171_, v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref(v___x_175_);
v_a_159_ = v_a_176_;
goto v___jp_158_;
}
else
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_175_);
v___x_178_ = l_Lean_Json_getStr_x3f(v_a_177_);
v___y_167_ = v___x_178_;
goto v___jp_166_;
}
}
default: 
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3));
v___x_180_ = lean_unsigned_to_nat(80u);
v___x_181_ = l_Lean_Json_pretty(v_val_171_, v___x_180_);
v___x_182_ = lean_string_append(v___x_179_, v___x_181_);
lean_dec_ref(v___x_181_);
v_a_159_ = v___x_182_;
goto v___jp_158_;
}
}
}
else
{
lean_object* v_label_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_label_183_ = lean_ctor_get(v_item_157_, 0);
lean_inc_ref(v_label_183_);
lean_dec_ref(v_item_157_);
v___x_184_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4));
v___x_185_ = lean_string_append(v___x_184_, v_label_183_);
lean_dec_ref(v_label_183_);
v_a_159_ = v___x_185_;
goto v___jp_158_;
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0));
v___x_161_ = ((lean_object*)(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1));
v___x_162_ = lean_unsigned_to_nat(144u);
v___x_163_ = lean_unsigned_to_nat(22u);
v___x_164_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_161_, v___x_162_, v___x_163_, v_a_159_);
lean_dec_ref(v_a_159_);
v___x_165_ = l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(v___x_164_);
return v___x_165_;
}
v___jp_166_:
{
if (lean_obj_tag(v___y_167_) == 0)
{
lean_object* v_a_168_; 
v_a_168_ = lean_ctor_get(v___y_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v___y_167_);
v_a_159_ = v_a_168_;
goto v___jp_158_;
}
else
{
lean_object* v_a_169_; 
v_a_169_ = lean_ctor_get(v___y_167_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v___y_167_);
return v_a_169_;
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileSource(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileSource(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileSource(builtin);
}
#ifdef __cplusplus
}
#endif
