// Lean compiler output
// Module: Init.Control
// Imports: Init.Control.Basic Init.Control.State Init.Control.StateRef Init.Control.Id Init.Control.Except Init.Control.Reader Init.Control.Option Init.Control.Lawful Init.Control.StateCps Init.Control.ExceptCps
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
lean_object* initialize_Init_Control_Basic(lean_object*);
lean_object* initialize_Init_Control_State(lean_object*);
lean_object* initialize_Init_Control_StateRef(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Option(lean_object*);
lean_object* initialize_Init_Control_Lawful(lean_object*);
lean_object* initialize_Init_Control_StateCps(lean_object*);
lean_object* initialize_Init_Control_ExceptCps(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateCps(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_ExceptCps(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
