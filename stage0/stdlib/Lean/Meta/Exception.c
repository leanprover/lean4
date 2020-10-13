// Lean compiler output
// Module: Lean.Meta.Exception
// Imports: Init Lean.Environment Lean.MetavarContext Lean.Message Lean.CoreM Lean.InternalExceptionId Lean.Util.PPGoal
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
lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_registerIsDefEqStuckId(lean_object*);
lean_object* l_Lean_Meta_registerIsDefEqStuckId___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerIsDefEqStuckId___closed__2;
static lean_object* _init_l_Lean_Meta_registerIsDefEqStuckId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isDefEqStuck");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_registerIsDefEqStuckId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_registerIsDefEqStuckId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_registerIsDefEqStuckId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_registerIsDefEqStuckId___closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
lean_object* initialize_Lean_InternalExceptionId(lean_object*);
lean_object* initialize_Lean_Util_PPGoal(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_registerIsDefEqStuckId___closed__1 = _init_l_Lean_Meta_registerIsDefEqStuckId___closed__1();
lean_mark_persistent(l_Lean_Meta_registerIsDefEqStuckId___closed__1);
l_Lean_Meta_registerIsDefEqStuckId___closed__2 = _init_l_Lean_Meta_registerIsDefEqStuckId___closed__2();
lean_mark_persistent(l_Lean_Meta_registerIsDefEqStuckId___closed__2);
res = l_Lean_Meta_registerIsDefEqStuckId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_isDefEqStuckExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_isDefEqStuckExceptionId);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
