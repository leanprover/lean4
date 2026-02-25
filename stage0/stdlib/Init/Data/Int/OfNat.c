// Lean compiler output
// Module: Init.Data.Int.OfNat
// Imports: public import Init.GrindInstances.ToInt public import Init.Data.Nat.Div.Basic import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Omega
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Int_Nonneg_num__cert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Nonneg_num__cert___closed__0;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Nonneg_num__cert(lean_object*);
LEAN_EXPORT lean_object* l_Int_Nonneg_num__cert___boxed(lean_object*);
static lean_object* _init_l_Int_Nonneg_num__cert___closed__0(void) {
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
x_2 = lean_obj_once(&l_Int_Nonneg_num__cert___closed__0, &l_Int_Nonneg_num__cert___closed__0_once, _init_l_Int_Nonneg_num__cert___closed__0);
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
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
