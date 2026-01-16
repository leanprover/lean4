// Lean compiler output
// Module: Std.Data.DTreeMap.DecidableEquiv
// Imports: public import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.Raw
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_beq___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_beq___redArg(x_3, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
