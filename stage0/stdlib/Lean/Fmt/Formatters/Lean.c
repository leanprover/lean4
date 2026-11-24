// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean
// Imports: public import Lean.Fmt.Formatters.Lean.Data public import Lean.Fmt.Formatters.Lean.Elab public import Lean.Fmt.Formatters.Lean.Exception public import Lean.Fmt.Formatters.Lean.LabelAttribute public import Lean.Fmt.Formatters.Lean.Linter public import Lean.Fmt.Formatters.Lean.Message public import Lean.Fmt.Formatters.Lean.Meta public import Lean.Fmt.Formatters.Lean.Parser public import Lean.Fmt.Formatters.Lean.PostprocessTraces public import Lean.Fmt.Formatters.Lean.PrettyPrinter public import Lean.Fmt.Formatters.Lean.Server public import Lean.Fmt.Formatters.Lean.Util public import Lean.Fmt.Formatters.Lean.Widget
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
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Data(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Linter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Server(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Widget(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Linter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Widget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Lean_Data(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Exception(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Linter(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Server(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Util(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Widget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Lean_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Linter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Widget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean(builtin);
}
#ifdef __cplusplus
}
#endif
