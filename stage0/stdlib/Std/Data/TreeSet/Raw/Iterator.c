// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Iterator
// Imports: public import Std.Data.TreeSet.Raw.Basic public import Std.Data.TreeMap.Raw.Iterator public import Std.Data.DTreeMap.Raw.Lemmas
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___redArg___boxed(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_TreeSet_Raw_iter___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_iter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_TreeSet_Raw_iter(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Raw_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Raw_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
