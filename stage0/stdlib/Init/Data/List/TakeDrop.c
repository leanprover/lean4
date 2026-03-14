// Lean compiler output
// Module: Init.Data.List.TakeDrop
// Imports: import all Init.Data.List.Basic public import Init.BinderPredicates public import Init.Ext import Init.ByCases import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.Nat.Div.Basic import Init.Data.Option.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_1_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_object* v___x_8_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_8_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_8_;
}
else
{
lean_object* v_one_9_; lean_object* v_n_10_; 
lean_dec(v_h__1_3_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_n_10_ = lean_nat_sub(v_x_1_, v_one_9_);
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_11_; 
lean_dec(v_h__3_5_);
v___x_11_ = lean_apply_1(v_h__2_4_, v_n_10_);
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_4_);
v_head_12_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_12_);
v_tail_13_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_13_);
lean_dec_ref(v_x_2_);
v___x_14_ = lean_apply_3(v_h__3_5_, v_n_10_, v_head_12_, v_tail_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(v_x_15_, v_x_16_, v_h__1_17_, v_h__2_18_, v_h__3_19_);
lean_dec(v_x_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_, lean_object* v_h__3_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(v_x_23_, v_x_24_, v_h__1_25_, v_h__2_26_, v_h__3_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_, lean_object* v_h__3_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(v_00_u03b1_29_, v_motive_30_, v_x_31_, v_x_32_, v_h__1_33_, v_h__2_34_, v_h__3_35_);
lean_dec(v_x_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(lean_object* v_b_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_b_37_) == 0)
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
v_val_42_ = lean_ctor_get(v_b_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_b_37_);
v___x_43_ = lean_apply_1(v_h__2_39_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_b_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(v_b_46_, v_h__1_47_, v_h__2_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_52_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__1_51_, v___x_53_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_51_);
v_head_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_head_55_);
v_tail_56_ = lean_ctor_get(v_x_50_, 1);
lean_inc(v_tail_56_);
lean_dec_ref(v_x_50_);
v___x_57_ = lean_apply_2(v_h__2_52_, v_head_55_, v_tail_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(v_x_60_, v_h__1_61_, v_h__2_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(uint8_t v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (v_x_64_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_65_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__2_66_, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_66_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_65_, v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
uint8_t v_x_22__boxed_74_; lean_object* v_res_75_; 
v_x_22__boxed_74_ = lean_unbox(v_x_71_);
v_res_75_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_74_, v_h__1_72_, v_h__2_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(lean_object* v_motive_76_, uint8_t v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(v_x_77_, v_h__1_78_, v_h__2_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
uint8_t v_x_33__boxed_85_; lean_object* v_res_86_; 
v_x_33__boxed_85_ = lean_unbox(v_x_82_);
v_res_86_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(v_motive_81_, v_x_33__boxed_85_, v_h__1_83_, v_h__2_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(lean_object* v_x_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_88_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__2_89_, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_93_; 
lean_dec(v_h__2_89_);
v_val_92_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_val_92_);
lean_dec_ref(v_x_87_);
v___x_93_ = lean_apply_1(v_h__1_88_, v_val_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(lean_object* v_00_u03b1_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(v_x_96_, v_h__1_97_, v_h__2_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_102_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__1_101_, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_101_);
v_val_105_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v_x_100_);
v___x_106_ = lean_apply_1(v_h__2_102_, v_val_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_107_, lean_object* v_motive_108_, lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(v_x_109_, v_h__1_110_, v_h__2_111_);
return v___x_112_;
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
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
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
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
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_TakeDrop(builtin);
}
#ifdef __cplusplus
}
#endif
