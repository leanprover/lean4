// Lean compiler output
// Module: Init.Data.List.Count
// Imports: import Init.Grind.Util public import Init.BinderPredicates public import Init.Ext public import Init.NotationExtra import Init.ByCases import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.List.Sublist import Init.Data.Option.Lemmas import Init.TacticsExtra
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v_head_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref_known(v_x_1_, 2);
v___x_8_ = lean_apply_3(v_h__2_4_, v_head_6_, v_tail_7_, v_x_2_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_15_; 
lean_dec(v_h__2_14_);
v___x_15_ = lean_apply_1(v_h__1_13_, v_x_12_);
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_13_);
v_head_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_x_11_, 2);
v___x_18_ = lean_apply_3(v_h__2_14_, v_head_16_, v_tail_17_, v_x_12_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
if (lean_obj_tag(v_ys_19_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_21_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_20_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_20_);
v_head_24_ = lean_ctor_get(v_ys_19_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_ys_19_, 1);
lean_inc(v_tail_25_);
lean_dec_ref_known(v_ys_19_, 2);
v___x_26_ = lean_apply_2(v_h__2_21_, v_head_24_, v_tail_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_27_, lean_object* v_motive_28_, lean_object* v_ys_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_ys_29_) == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_31_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_apply_1(v_h__1_30_, v___x_32_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_30_);
v_head_34_ = lean_ctor_get(v_ys_29_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_ys_29_, 1);
lean_inc(v_tail_35_);
lean_dec_ref_known(v_ys_29_, 2);
v___x_36_ = lean_apply_2(v_h__2_31_, v_head_34_, v_tail_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_38_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_38_);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v_x_37_, 1);
v___x_43_ = lean_apply_1(v_h__2_39_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_47_);
v_val_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_x_46_, 1);
v___x_52_ = lean_apply_1(v_h__2_48_, v_val_51_);
return v___x_52_;
}
}
}
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Count(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Count(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Count(builtin);
}
#ifdef __cplusplus
}
#endif
