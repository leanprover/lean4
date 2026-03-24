// Lean compiler output
// Module: Init.Data.List.Sort.Lemmas
// Imports: public import Init.Data.List.Sort.Basic import all Init.Data.List.Sort.Basic public import Init.BinderPredicates public import Init.Data.Bool import Init.Data.List.Nat.Range import Init.Data.List.Pairwise import Init.Data.List.Perm import Init.Data.List.Range import Init.Data.List.Sublist import Init.Data.Nat.Linear import Init.Data.Prod
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
if (lean_obj_tag(v_xs_1_) == 0)
{
lean_object* v___x_6_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_6_ = lean_apply_1(v_h__1_3_, v_ys_2_);
return v___x_6_;
}
else
{
lean_dec(v_h__1_3_);
if (lean_obj_tag(v_ys_2_) == 0)
{
lean_object* v___x_7_; 
lean_dec(v_h__3_5_);
v___x_7_ = lean_apply_2(v_h__2_4_, v_xs_1_, lean_box(0));
return v___x_7_;
}
else
{
lean_object* v_head_8_; lean_object* v_tail_9_; lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_12_; 
lean_dec(v_h__2_4_);
v_head_8_ = lean_ctor_get(v_xs_1_, 0);
lean_inc(v_head_8_);
v_tail_9_ = lean_ctor_get(v_xs_1_, 1);
lean_inc(v_tail_9_);
lean_dec_ref(v_xs_1_);
v_head_10_ = lean_ctor_get(v_ys_2_, 0);
lean_inc(v_head_10_);
v_tail_11_ = lean_ctor_get(v_ys_2_, 1);
lean_inc(v_tail_11_);
lean_dec_ref(v_ys_2_);
v___x_12_ = lean_apply_4(v_h__3_5_, v_head_8_, v_tail_9_, v_head_10_, v_tail_11_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter(lean_object* v_00_u03b1_13_, lean_object* v_motive_14_, lean_object* v_xs_15_, lean_object* v_ys_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
if (lean_obj_tag(v_xs_15_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v___x_20_ = lean_apply_1(v_h__1_17_, v_ys_16_);
return v___x_20_;
}
else
{
lean_dec(v_h__1_17_);
if (lean_obj_tag(v_ys_16_) == 0)
{
lean_object* v___x_21_; 
lean_dec(v_h__3_19_);
v___x_21_ = lean_apply_2(v_h__2_18_, v_xs_15_, lean_box(0));
return v___x_21_;
}
else
{
lean_object* v_head_22_; lean_object* v_tail_23_; lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_18_);
v_head_22_ = lean_ctor_get(v_xs_15_, 0);
lean_inc(v_head_22_);
v_tail_23_ = lean_ctor_get(v_xs_15_, 1);
lean_inc(v_tail_23_);
lean_dec_ref(v_xs_15_);
v_head_24_ = lean_ctor_get(v_ys_16_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_ys_16_, 1);
lean_inc(v_tail_25_);
lean_dec_ref(v_ys_16_);
v___x_26_ = lean_apply_4(v_h__3_19_, v_head_22_, v_tail_23_, v_head_24_, v_tail_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_32_; 
lean_dec(v_h__3_31_);
lean_dec(v_h__2_30_);
v___x_32_ = lean_apply_1(v_h__1_29_, v_x_28_);
return v___x_32_;
}
else
{
lean_object* v_tail_33_; 
lean_dec(v_h__1_29_);
v_tail_33_ = lean_ctor_get(v_x_27_, 1);
if (lean_obj_tag(v_tail_33_) == 0)
{
lean_object* v_head_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_31_);
v_head_34_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_34_);
lean_dec_ref(v_x_27_);
v___x_35_ = lean_apply_2(v_h__2_30_, v_head_34_, v_x_28_);
return v___x_35_;
}
else
{
lean_object* v_head_36_; lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_39_; 
lean_inc_ref(v_tail_33_);
lean_dec(v_h__2_30_);
v_head_36_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_36_);
lean_dec_ref(v_x_27_);
v_head_37_ = lean_ctor_get(v_tail_33_, 0);
lean_inc(v_head_37_);
v_tail_38_ = lean_ctor_get(v_tail_33_, 1);
lean_inc(v_tail_38_);
lean_dec_ref(v_tail_33_);
v___x_39_ = lean_apply_4(v_h__3_31_, v_head_36_, v_head_37_, v_tail_38_, v_x_28_);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter(lean_object* v_00_u03b1_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_47_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v___x_47_ = lean_apply_1(v_h__1_44_, v_x_43_);
return v___x_47_;
}
else
{
lean_object* v_tail_48_; 
lean_dec(v_h__1_44_);
v_tail_48_ = lean_ctor_get(v_x_42_, 1);
if (lean_obj_tag(v_tail_48_) == 0)
{
lean_object* v_head_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_46_);
v_head_49_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_head_49_);
lean_dec_ref(v_x_42_);
v___x_50_ = lean_apply_2(v_h__2_45_, v_head_49_, v_x_43_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_head_52_; lean_object* v_tail_53_; lean_object* v___x_54_; 
lean_inc_ref(v_tail_48_);
lean_dec(v_h__2_45_);
v_head_51_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_head_51_);
lean_dec_ref(v_x_42_);
v_head_52_ = lean_ctor_get(v_tail_48_, 0);
lean_inc(v_head_52_);
v_tail_53_ = lean_ctor_get(v_tail_48_, 1);
lean_inc(v_tail_53_);
lean_dec_ref(v_tail_48_);
v___x_54_ = lean_apply_4(v_h__3_46_, v_head_51_, v_head_52_, v_tail_53_, v_x_43_);
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_59_; 
lean_dec(v_h__2_58_);
v___x_59_ = lean_apply_1(v_h__1_57_, v_x_56_);
return v___x_59_;
}
else
{
lean_object* v_head_60_; lean_object* v_tail_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_57_);
v_head_60_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_head_60_);
v_tail_61_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_tail_61_);
lean_dec_ref(v_x_55_);
v___x_62_ = lean_apply_3(v_h__2_58_, v_head_60_, v_tail_61_, v_x_56_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_63_, lean_object* v_motive_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_69_; 
lean_dec(v_h__2_68_);
v___x_69_ = lean_apply_1(v_h__1_67_, v_x_66_);
return v___x_69_;
}
else
{
lean_object* v_head_70_; lean_object* v_tail_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_67_);
v_head_70_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_head_70_);
v_tail_71_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_tail_71_);
lean_dec_ref(v_x_65_);
v___x_72_ = lean_apply_3(v_h__2_68_, v_head_70_, v_tail_71_, v_x_66_);
return v___x_72_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Sort_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Sort_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
