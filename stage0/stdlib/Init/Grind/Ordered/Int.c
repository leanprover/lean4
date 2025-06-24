// Lean compiler output
// Module: Init.Grind.Ordered.Int
// Imports: Init.Grind.Ordered.Ring Init.GrindInstances.Ring.Int Init.Omega
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
static lean_object* l_Lean_Grind_instLinearOrderInt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_instLinearOrderInt;
static lean_object* _init_l_Lean_Grind_instLinearOrderInt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instLinearOrderInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instLinearOrderInt___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ordered_Int(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instLinearOrderInt___closed__0 = _init_l_Lean_Grind_instLinearOrderInt___closed__0();
lean_mark_persistent(l_Lean_Grind_instLinearOrderInt___closed__0);
l_Lean_Grind_instLinearOrderInt = _init_l_Lean_Grind_instLinearOrderInt();
lean_mark_persistent(l_Lean_Grind_instLinearOrderInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
