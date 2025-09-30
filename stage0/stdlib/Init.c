// Lean compiler output
// Module: Init
// Imports: public import Init.Prelude public import Init.Notation public import Init.Tactics public import Init.TacticsExtra public import Init.ByCases public import Init.RCases public import Init.Core public import Init.Control public import Init.Data.Basic public import Init.WF public import Init.WFTactics public import Init.Data public import Init.System public import Init.Util public import Init.Dynamic public import Init.ShareCommon public import Init.MetaTypes public import Init.Meta public import Init.NotationExtra public import Init.SimpLemmas public import Init.PropLemmas public import Init.Hints public import Init.Conv public import Init.Guard public import Init.Simproc public import Init.SizeOfLemmas public import Init.BinderPredicates public import Init.Ext public import Init.Omega public import Init.MacroTrace public import Init.Grind public import Init.GrindInstances public import Init.While public import Init.Syntax public import Init.Internal public import Init.Try public meta import Init.Try public import Init.BinderNameHint public import Init.Task public import Init.MethodSpecsSimp public import Init.LawfulBEqTactics
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
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WF(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WFTactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Dynamic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Init_MetaTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_PropLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Hints(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Guard(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_SizeOfLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
lean_object* initialize_Init_MacroTrace(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances(uint8_t builtin, lean_object*);
lean_object* initialize_Init_While(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Init_BinderNameHint(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Task(uint8_t builtin, lean_object*);
lean_object* initialize_Init_MethodSpecsSimp(uint8_t builtin, lean_object*);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Dynamic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Hints(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Guard(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SizeOfLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MacroTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Task(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MethodSpecsSimp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
