// Lean compiler output
// Module: Init.Data.List.ToArray
// Imports: import all Init.Data.List.Control public import Init.Data.List.Monadic import all Init.Data.Array.Basic import all Init.Data.Array.Set import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Bool import Init.Data.List.Erase import Init.Data.List.Find import Init.Data.List.Nat.Erase import Init.Data.List.Nat.InsertIdx import Init.Data.List.Nat.TakeDrop import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.List.Zip import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas import Init.Omega import Init.TacticsExtra
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object* v_____do__lift_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_____do__lift_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_____do__lift_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_a_13_ = lean_ctor_get(v_____do__lift_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_____do__lift_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_a_15_ = lean_ctor_get(v_____do__lift_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_____do__lift_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v_a_20_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v_x_17_, 1);
v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_a_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_x_17_, 1);
v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v_a_29_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v_x_26_, 1);
v___x_30_ = lean_apply_1(v_h__1_27_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_a_31_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_x_26_, 1);
v___x_32_ = lean_apply_1(v_h__2_28_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_____do__lift_33_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_35_);
v_val_36_ = lean_ctor_get(v_____do__lift_33_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v_____do__lift_33_, 1);
v___x_37_ = lean_apply_1(v_h__1_34_, v_val_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; 
lean_dec(v_h__1_34_);
v___x_38_ = lean_apply_2(v_h__2_35_, v_____do__lift_33_, lean_box(0));
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_39_, lean_object* v_motive_40_, lean_object* v_____do__lift_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_41_) == 1)
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_43_);
v_val_44_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_____do__lift_41_, 1);
v___x_45_ = lean_apply_1(v_h__1_42_, v_val_44_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; 
lean_dec(v_h__1_42_);
v___x_46_ = lean_apply_2(v_h__2_43_, v_____do__lift_41_, lean_box(0));
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__2_49_, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_49_);
v_val_52_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v_x_47_, 1);
v___x_53_ = lean_apply_1(v_h__1_48_, v_val_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_57_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__2_58_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_58_);
v_val_61_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v_x_56_, 1);
v___x_62_ = lean_apply_1(v_h__1_57_, v_val_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_____do__lift_63_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_64_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__2_65_, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; 
lean_dec(v_h__2_65_);
v_val_68_ = lean_ctor_get(v_____do__lift_63_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v_____do__lift_63_, 1);
v___x_69_ = lean_apply_1(v_h__1_64_, v_val_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_70_, lean_object* v_motive_71_, lean_object* v_____do__lift_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (lean_obj_tag(v_____do__lift_72_) == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_73_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__2_74_, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v_val_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_74_);
v_val_77_ = lean_ctor_get(v_____do__lift_72_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_____do__lift_72_, 1);
v___x_78_ = lean_apply_1(v_h__1_73_, v_val_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_r_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__2_81_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_81_);
v_val_84_ = lean_ctor_get(v_r_79_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_r_79_, 1);
v___x_85_ = lean_apply_1(v_h__1_80_, v_val_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_86_, lean_object* v_motive_87_, lean_object* v_r_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_r_88_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_89_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__2_90_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
lean_dec(v_h__2_90_);
v_val_93_ = lean_ctor_get(v_r_88_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v_r_88_, 1);
v___x_94_ = lean_apply_1(v_h__1_89_, v_val_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (v_____do__lift_95_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_h__1_96_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_apply_1(v_h__2_97_, v___x_98_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_97_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__1_96_, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
uint8_t v_____do__lift_24__boxed_105_; lean_object* v_res_106_; 
v_____do__lift_24__boxed_105_ = lean_unbox(v_____do__lift_102_);
v_res_106_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_105_, v_h__1_103_, v_h__2_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* v_motive_107_, uint8_t v_____do__lift_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (v_____do__lift_108_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__1_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__2_110_, v___x_111_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_110_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__1_109_, v___x_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_115_, lean_object* v_____do__lift_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
uint8_t v_____do__lift_35__boxed_119_; lean_object* v_res_120_; 
v_____do__lift_35__boxed_119_ = lean_unbox(v_____do__lift_116_);
v_res_120_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(v_motive_115_, v_____do__lift_35__boxed_119_, v_h__1_117_, v_h__2_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (v_x_121_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_122_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_apply_1(v_h__2_123_, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__2_123_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__1_122_, v___x_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
uint8_t v_x_24__boxed_131_; lean_object* v_res_132_; 
v_x_24__boxed_131_ = lean_unbox(v_x_128_);
v_res_132_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_131_, v_h__1_129_, v_h__2_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* v_motive_133_, uint8_t v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
if (v_x_134_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__1_135_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__2_136_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_h__2_136_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_1(v_h__1_135_, v___x_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
uint8_t v_x_35__boxed_145_; lean_object* v_res_146_; 
v_x_35__boxed_145_ = lean_unbox(v_x_142_);
v_res_146_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(v_motive_141_, v_x_35__boxed_145_, v_h__1_143_, v_h__2_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_h__2_149_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_apply_1(v_h__1_148_, v___x_150_);
return v___x_151_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v_h__1_148_);
v_val_152_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v_x_147_, 1);
v___x_153_ = lean_apply_1(v_h__2_149_, v_val_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_154_, lean_object* v_as_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_159_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__1_158_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_163_; 
lean_dec(v_h__1_158_);
v_val_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v_x_157_, 1);
v___x_163_ = lean_apply_1(v_h__2_159_, v_val_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_164_, lean_object* v_as_165_, lean_object* v_motive_166_, lean_object* v_x_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(v_00_u03b1_164_, v_as_165_, v_motive_166_, v_x_167_, v_h__1_168_, v_h__2_169_);
lean_dec_ref(v_as_165_);
return v_res_170_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_ToArray(builtin);
}
#ifdef __cplusplus
}
#endif
