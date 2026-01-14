// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Lemmas
// Imports: import Std.Data.TreeMap.Raw.Lemmas import Std.Data.DTreeMap.Raw.Lemmas public import Std.Data.TreeSet.Raw.Basic public import Init.Data.List.BasicAux public import Init.Data.Order.ClassesExtra
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_Equiv_instTrans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_Equiv_instTrans___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_Equiv_instTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_Equiv_instTrans___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_TreeSet_Raw_Equiv_instTrans(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Std_Data_TreeMap_Raw_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Raw_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
