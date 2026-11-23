// Lean compiler output
// Module: Lean.Data.Markdown
// Imports: public import Lean.Data.Markdown.Unicode.CaseFolding public import Lean.Data.Markdown.Unicode.CharacterClasses public import Lean.Data.Markdown.Inline public import Lean.Data.Markdown.Block public import Lean.Data.Markdown.Text public import Lean.Data.Markdown.Parser
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
lean_object* runtime_initialize_Lean_Data_Markdown_Unicode_CaseFolding(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Unicode_CharacterClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Markdown_Unicode_CaseFolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Unicode_CharacterClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Markdown_Unicode_CaseFolding(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Unicode_CharacterClasses(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Markdown_Unicode_CaseFolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Unicode_CharacterClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown(builtin);
}
#ifdef __cplusplus
}
#endif
