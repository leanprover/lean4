// Lean compiler output
// Module: Init.Data.Int.OfNat
// Imports: public import Init.Data.Int.Linear public import Init.GrindInstances.ToInt
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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Int_Nonneg_num__cert___closed__0;
LEAN_EXPORT uint8_t l_Int_Nonneg_num__cert(lean_object*);
LEAN_EXPORT lean_object* l_Int_Nonneg_num__cert___boxed(lean_object*);
static lean_object* _init_l_Int_Nonneg_num__cert___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_Nonneg_num__cert(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_Nonneg_num__cert___closed__0;
x_3 = lean_int_dec_le(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Nonneg_num__cert___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Nonneg_num__cert(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_Nonneg_num__cert___closed__0 = _init_l_Int_Nonneg_num__cert___closed__0();
lean_mark_persistent(l_Int_Nonneg_num__cert___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
