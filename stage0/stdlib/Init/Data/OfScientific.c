// Lean compiler output
// Module: Init.Data.OfScientific
// Imports: Init.Meta Init.Data.Float Init.Data.Nat
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
double lean_float_of_scientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instOfScientificFloat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l_instOfScientificFloat(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT double l_instOfScientificFloat(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
double x_4; 
x_4 = lean_float_of_scientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instOfScientificFloat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; double x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instOfScientificFloat(x_1, x_4, x_3);
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* initialize_Init_Meta(lean_object*);
lean_object* initialize_Init_Data_Float(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_OfScientific(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
