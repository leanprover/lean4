// Lean compiler output
// Module: Std.Data.TreeSet.Iterator
// Imports: public import Std.Data.TreeSet.Basic public import Std.Data.TreeMap.Iterator public import Std.Data.DTreeMap.Lemmas import Init.Data.Iterators.Lemmas.Combinators.FilterMap
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
lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___redArg(lean_object* v_m_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___redArg___boxed(lean_object* v_m_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_TreeSet_iter___redArg(v_m_3_);
lean_dec(v_m_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_iter(lean_object* v_00_u03b1_5_, lean_object* v_cmp_6_, lean_object* v_m_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_iter___boxed(lean_object* v_00_u03b1_9_, lean_object* v_cmp_10_, lean_object* v_m_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_TreeSet_iter(v_00_u03b1_9_, v_cmp_10_, v_m_11_);
lean_dec(v_m_11_);
lean_dec_ref(v_cmp_10_);
return v_res_12_;
}
}
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
