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
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
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
LEAN_EXPORT void l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_95_ = stack[0].m_num;
lean_object* v_h__1_96_ = stack[1].m_obj;
lean_object* v_h__2_97_ = stack[2].m_obj;
lean_object* v_res_102_;
v_res_102_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_95_, v_h__1_96_, v_h__2_97_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
uint8_t v_____do__lift_24__boxed_106_; lean_object* v_res_107_; 
v_____do__lift_24__boxed_106_ = lean_unbox(v_____do__lift_103_);
v_res_107_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_106_, v_h__1_104_, v_h__2_105_);
return v_res_107_;
}
}
lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* v_motive_108_, uint8_t v_____do__lift_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (v_____do__lift_109_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_110_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__2_111_, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_111_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__1_110_, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_109_ = stack[1].m_num;
lean_object* v_h__1_110_ = stack[2].m_obj;
lean_object* v_h__2_111_ = stack[3].m_obj;
lean_object* v_res_116_;
v_res_116_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_box(0), v_____do__lift_109_, v_h__1_110_, v_h__2_111_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_117_, lean_object* v_____do__lift_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
uint8_t v_____do__lift_41__boxed_121_; lean_object* v_res_122_; 
v_____do__lift_41__boxed_121_ = lean_unbox(v_____do__lift_118_);
v_res_122_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(v_motive_117_, v_____do__lift_41__boxed_121_, v_h__1_119_, v_h__2_120_);
return v_res_122_;
}
}
lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
if (v_x_123_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_124_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__2_125_, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_125_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__1_124_, v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_123_ = stack[0].m_num;
lean_object* v_h__1_124_ = stack[1].m_obj;
lean_object* v_h__2_125_ = stack[2].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_123_, v_h__1_124_, v_h__2_125_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
uint8_t v_x_24__boxed_134_; lean_object* v_res_135_; 
v_x_24__boxed_134_ = lean_unbox(v_x_131_);
v_res_135_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_134_, v_h__1_132_, v_h__2_133_);
return v_res_135_;
}
}
lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* v_motive_136_, uint8_t v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
if (v_x_137_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_138_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_apply_1(v_h__2_139_, v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_139_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__1_138_, v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_137_ = stack[1].m_num;
lean_object* v_h__1_138_ = stack[2].m_obj;
lean_object* v_h__2_139_ = stack[3].m_obj;
lean_object* v_res_144_;
v_res_144_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_box(0), v_x_137_, v_h__1_138_, v_h__2_139_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
uint8_t v_x_41__boxed_149_; lean_object* v_res_150_; 
v_x_41__boxed_149_ = lean_unbox(v_x_146_);
v_res_150_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(v_motive_145_, v_x_41__boxed_149_, v_h__1_147_, v_h__2_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_155_; 
lean_dec(v_h__2_154_);
v___x_155_ = lean_apply_2(v_h__1_153_, v_x_152_, lean_box(0));
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; lean_object* v___x_158_; 
lean_dec(v_h__1_153_);
v_head_156_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_head_156_);
v_tail_157_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_tail_157_);
lean_dec_ref_known(v_x_151_, 2);
v___x_158_ = lean_apply_4(v_h__2_154_, v_head_156_, v_tail_157_, v_x_152_, lean_box(0));
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object* v_00_u03b1_159_, lean_object* v_l_160_, lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_h__2_166_);
v___x_167_ = lean_apply_2(v_h__1_165_, v_x_163_, lean_box(0));
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_165_);
v_head_168_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_tail_169_);
lean_dec_ref_known(v_x_162_, 2);
v___x_170_ = lean_apply_4(v_h__2_166_, v_head_168_, v_tail_169_, v_x_163_, lean_box(0));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object* v_00_u03b1_171_, lean_object* v_l_172_, lean_object* v_motive_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Init_Data_List_ToArray_0__List_findFinIdx_x3f_go_match__1_splitter(v_00_u03b1_171_, v_l_172_, v_motive_173_, v_x_174_, v_x_175_, v_x_176_, v_h__1_177_, v_h__2_178_);
lean_dec(v_l_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_182_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__1_181_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_186_; 
lean_dec(v_h__1_181_);
v_val_185_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v_x_180_, 1);
v___x_186_ = lean_apply_1(v_h__2_182_, v_val_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_187_, lean_object* v_as_188_, lean_object* v_motive_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_h__2_192_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_1(v_h__1_191_, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_val_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_191_);
v_val_195_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v_x_190_, 1);
v___x_196_ = lean_apply_1(v_h__2_192_, v_val_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_197_, lean_object* v_as_198_, lean_object* v_motive_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(v_00_u03b1_197_, v_as_198_, v_motive_199_, v_x_200_, v_h__1_201_, v_h__2_202_);
lean_dec_ref(v_as_198_);
return v_res_203_;
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
