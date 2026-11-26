// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do
// Imports: public import Lean.Fmt.Formatters.Std.Do.PostCond public import Lean.Fmt.Formatters.Std.Do.SPred public import Lean.Fmt.Formatters.Std.Do.Triple public import Lean.Fmt.Formatters.Std.Do.WP
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
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_WP(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_PostCond(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_SPred(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_Triple(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_WP(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_Do_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_Do_Triple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do(builtin);
}
#ifdef __cplusplus
}
#endif
