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
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_x_23_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec(v_h__3_27_);
lean_dec(v_h__2_26_);
v___x_30_ = lean_apply_1(v_h__1_25_, v_x_24_);
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; 
lean_dec(v_h__1_25_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_x_23_, v_one_31_);
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h__3_27_);
v___x_33_ = lean_apply_1(v_h__2_26_, v_n_32_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_26_);
v_head_34_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_x_24_, 1);
lean_inc(v_tail_35_);
lean_dec_ref(v_x_24_);
v___x_36_ = lean_apply_3(v_h__3_27_, v_n_32_, v_head_34_, v_tail_35_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_37_, lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(v_00_u03b1_37_, v_motive_38_, v_x_39_, v_x_40_, v_h__1_41_, v_h__2_42_, v_h__3_43_);
lean_dec(v_x_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(lean_object* v_b_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_b_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_val_50_ = lean_ctor_get(v_b_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_b_45_);
v___x_51_ = lean_apply_1(v_h__2_47_, v_val_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(lean_object* v_00_u03b1_52_, lean_object* v_motive_53_, lean_object* v_b_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_b_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__1_55_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_55_);
v_val_59_ = lean_ctor_get(v_b_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_b_54_);
v___x_60_ = lean_apply_1(v_h__2_56_, v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_63_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_62_, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_head_66_; lean_object* v_tail_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_62_);
v_head_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_66_);
v_tail_67_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_tail_67_);
lean_dec_ref(v_x_61_);
v___x_68_ = lean_apply_2(v_h__2_63_, v_head_66_, v_tail_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_73_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__1_72_, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_72_);
v_head_76_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_76_);
v_tail_77_ = lean_ctor_get(v_x_71_, 1);
lean_inc(v_tail_77_);
lean_dec_ref(v_x_71_);
v___x_78_ = lean_apply_2(v_h__2_73_, v_head_76_, v_tail_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(uint8_t v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (v_x_79_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__2_81_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_81_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_80_, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
uint8_t v_x_26__boxed_89_; lean_object* v_res_90_; 
v_x_26__boxed_89_ = lean_unbox(v_x_86_);
v_res_90_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_89_, v_h__1_87_, v_h__2_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(lean_object* v_motive_91_, uint8_t v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (v_x_92_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_h__1_93_);
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_1(v_h__2_94_, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_h__2_94_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_apply_1(v_h__1_93_, v___x_97_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
uint8_t v_x_37__boxed_103_; lean_object* v_res_104_; 
v_x_37__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(v_motive_99_, v_x_37__boxed_103_, v_h__1_101_, v_h__2_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__2_107_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v_val_110_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_110_);
lean_dec_ref(v_x_105_);
v___x_111_ = lean_apply_1(v_h__1_106_, v_val_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(lean_object* v_00_u03b1_112_, lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_115_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__2_116_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_116_);
v_val_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_x_114_);
v___x_120_ = lean_apply_1(v_h__1_115_, v_val_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_h__2_123_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_apply_1(v_h__1_122_, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_122_);
v_val_126_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_val_126_);
lean_dec_ref(v_x_121_);
v___x_127_ = lean_apply_1(v_h__2_123_, v_val_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__2_132_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__1_131_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_131_);
v_val_135_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v_x_130_);
v___x_136_ = lean_apply_1(v_h__2_132_, v_val_135_);
return v___x_136_;
}
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
