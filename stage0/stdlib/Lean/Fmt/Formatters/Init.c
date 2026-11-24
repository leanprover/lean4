// Lean compiler output
// Module: Lean.Fmt.Formatters.Init
// Imports: public import Lean.Fmt.Formatters.Init.Notation public import Lean.Fmt.Formatters.Init.NotationExtra public import Lean.Fmt.Formatters.Init.Tactics public import Lean.Fmt.Formatters.Init.TacticsExtra public import Lean.Fmt.Formatters.Init.ByCases public import Lean.Fmt.Formatters.Init.Meta public import Lean.Fmt.Formatters.Init.RCases public import Lean.Fmt.Formatters.Init.Core public import Lean.Fmt.Formatters.Init.GetElem public import Lean.Fmt.Formatters.Init.Ext public import Lean.Fmt.Formatters.Init.WFTactics public import Lean.Fmt.Formatters.Init.BinderPredicates public import Lean.Fmt.Formatters.Init.MacroTrace public import Lean.Fmt.Formatters.Init.System public import Lean.Fmt.Formatters.Init.Data public import Lean.Fmt.Formatters.Init.Conv public import Lean.Fmt.Formatters.Init.Guard public import Lean.Fmt.Formatters.Init.Grind public import Lean.Fmt.Formatters.Init.Data public import Lean.Fmt.Formatters.Init.Simproc public import Lean.Fmt.Formatters.Init.CbvSimproc public import Lean.Fmt.Formatters.Init.Sym public import Lean.Fmt.Formatters.Init.Try
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
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_MacroTrace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_System(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Conv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Guard(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Sym(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Try(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_ByCases(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Meta(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_RCases(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Core(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_GetElem(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Ext(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_MacroTrace(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_System(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Data(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Conv(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Guard(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Data(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Sym(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Try(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init(builtin);
}
#ifdef __cplusplus
}
#endif
