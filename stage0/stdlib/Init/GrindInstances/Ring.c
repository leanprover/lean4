// Lean compiler output
// Module: Init.GrindInstances.Ring
// Imports: Init.GrindInstances.Ring.Nat Init.GrindInstances.Ring.Int Init.GrindInstances.Ring.UInt Init.GrindInstances.Ring.SInt Init.GrindInstances.Ring.Fin Init.GrindInstances.Ring.BitVec
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
lean_object* initialize_Init_GrindInstances_Ring_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_Fin(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_BitVec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GrindInstances_Ring_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_SInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
