// Lean compiler output
// Module: Init.Grind.CommRing
// Imports: Init.Grind.CommRing.Basic Init.Grind.CommRing.Int Init.Grind.CommRing.UInt Init.Grind.CommRing.SInt Init.Grind.CommRing.Fin Init.Grind.CommRing.BitVec Init.Grind.CommRing.Poly
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
lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_UInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_SInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_Fin(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_Poly(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_SInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
