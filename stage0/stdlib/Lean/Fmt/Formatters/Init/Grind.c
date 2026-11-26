// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind
// Imports: public import Lean.Fmt.Formatters.Init.Grind.Attr public import Lean.Fmt.Formatters.Init.Grind.Annotated public import Lean.Fmt.Formatters.Init.Grind.Interactive public import Lean.Fmt.Formatters.Init.Grind.Tactics public import Lean.Fmt.Formatters.Init.Grind.Lint public import Lean.Fmt.Formatters.Init.Grind.Propagator
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
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Attr(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Lint(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind(builtin);
}
#ifdef __cplusplus
}
#endif
