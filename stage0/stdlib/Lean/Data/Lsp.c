// Lean compiler output
// Module: Lean.Data.Lsp
// Imports: Init Lean.Data.Lsp.Basic Lean.Data.Lsp.Capabilities Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Data.Lsp.InitShutdown Lean.Data.Lsp.LanguageFeatures Lean.Data.Lsp.TextSync Lean.Data.Lsp.Utf16 Lean.Data.Lsp.Workspace Lean.Data.Lsp.Ipc
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Capabilities(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(lean_object*);
lean_object* initialize_Lean_Data_Lsp_InitShutdown(lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(lean_object*);
lean_object* initialize_Lean_Data_Lsp_TextSync(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Workspace(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Ipc(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Capabilities(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_InitShutdown(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_TextSync(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Workspace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Ipc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
