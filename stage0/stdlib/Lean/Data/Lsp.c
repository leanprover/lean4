// Lean compiler output
// Module: Lean.Data.Lsp
// Imports: Lean.Data.Lsp.Basic Lean.Data.Lsp.Capabilities Lean.Data.Lsp.Client Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Data.Lsp.InitShutdown Lean.Data.Lsp.Internal Lean.Data.Lsp.LanguageFeatures Lean.Data.Lsp.TextSync Lean.Data.Lsp.Utf16 Lean.Data.Lsp.Workspace Lean.Data.Lsp.Ipc Lean.Data.Lsp.CodeActions
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
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Client(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_InitShutdown(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_TextSync(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_CodeActions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Capabilities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Client(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_InitShutdown(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_TextSync(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Ipc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_CodeActions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
