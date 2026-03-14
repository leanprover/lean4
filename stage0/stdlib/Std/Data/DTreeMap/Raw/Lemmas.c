// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.Lemmas
// Imports: import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.Raw.AdditionalOperations public import Init.Data.Array.Perm import Init.Data.List.Find import Init.Data.List.Pairwise import Init.Data.Prod
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeTypeForall__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Equiv_instTrans(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Equiv_instTrans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeTypeForall__1(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Equiv_instTrans(lean_object* v_00_u03b1_3_, lean_object* v_00_u03b2_4_, lean_object* v_cmp_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Equiv_instTrans___boxed(lean_object* v_00_u03b1_7_, lean_object* v_00_u03b2_8_, lean_object* v_cmp_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_DTreeMap_Raw_Equiv_instTrans(v_00_u03b1_7_, v_00_u03b2_8_, v_cmp_9_);
lean_dec_ref(v_cmp_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_1(v_h__2_13_, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_val_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_16_);
lean_dec_ref(v_x_11_);
v___x_17_ = lean_apply_1(v_h__1_12_, v_val_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter___redArg(v_x_20_, v_h__1_21_, v_h__2_22_);
return v___x_23_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
