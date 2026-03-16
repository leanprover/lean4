// Lean compiler output
// Module: Init.Data.List.Monadic
// Imports: public import Init.Data.List.Attach import all Init.Data.List.Control import Init.Data.Array.Bootstrap import Init.Data.Bool
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
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg___lam__0(lean_object* v_____do__lift_1_, lean_object* v_toPure_2_, lean_object* v_____do__lift_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4_, 0, v_____do__lift_1_);
lean_ctor_set(v___x_4_, 1, v_____do__lift_3_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg(lean_object* v_inst_6_, lean_object* v_f_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v_toApplicative_9_; lean_object* v_toPure_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_toApplicative_9_ = lean_ctor_get(v_inst_6_, 0);
lean_inc_ref(v_toApplicative_9_);
lean_dec(v_f_7_);
lean_dec_ref(v_inst_6_);
v_toPure_10_ = lean_ctor_get(v_toApplicative_9_, 1);
lean_inc(v_toPure_10_);
lean_dec_ref(v_toApplicative_9_);
v___x_11_ = lean_box(0);
v___x_12_ = lean_apply_2(v_toPure_10_, lean_box(0), v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_toApplicative_13_; lean_object* v_toBind_14_; lean_object* v_toPure_15_; lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_toApplicative_13_ = lean_ctor_get(v_inst_6_, 0);
v_toBind_14_ = lean_ctor_get(v_inst_6_, 1);
lean_inc(v_toBind_14_);
v_toPure_15_ = lean_ctor_get(v_toApplicative_13_, 1);
lean_inc(v_toPure_15_);
v_head_16_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_tail_17_);
lean_dec_ref(v_x_8_);
lean_inc(v_toBind_14_);
lean_inc(v_f_7_);
v___f_18_ = lean_alloc_closure((void*)(l_List_mapM_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_18_, 0, v_toPure_15_);
lean_closure_set(v___f_18_, 1, v_inst_6_);
lean_closure_set(v___f_18_, 2, v_f_7_);
lean_closure_set(v___f_18_, 3, v_tail_17_);
lean_closure_set(v___f_18_, 4, v_toBind_14_);
v___x_19_ = lean_apply_1(v_f_7_, v_head_16_);
v___x_20_ = lean_apply_4(v_toBind_14_, lean_box(0), lean_box(0), v___x_19_, v___f_18_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_x27___redArg___lam__1(lean_object* v_toPure_21_, lean_object* v_inst_22_, lean_object* v_f_23_, lean_object* v_tail_24_, lean_object* v_toBind_25_, lean_object* v_____do__lift_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___f_27_ = lean_alloc_closure((void*)(l_List_mapM_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_27_, 0, v_____do__lift_26_);
lean_closure_set(v___f_27_, 1, v_toPure_21_);
v___x_28_ = l_List_mapM_x27___redArg(v_inst_22_, v_f_23_, v_tail_24_);
v___x_29_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v___x_28_, v___f_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_x27(lean_object* v_m_30_, lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_f_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_List_mapM_x27___redArg(v_inst_33_, v_f_34_, v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_41_; 
lean_dec(v_h__2_40_);
v___x_41_ = lean_apply_1(v_h__1_39_, v_x_38_);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_39_);
v_head_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref(v_x_37_);
v___x_44_ = lean_apply_3(v_h__2_40_, v_head_42_, v_tail_43_, v_x_38_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(v_x_48_, v_x_49_, v_h__1_50_, v_h__2_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_55_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_apply_1(v_h__1_54_, v___x_56_);
return v___x_57_;
}
else
{
lean_object* v_head_58_; lean_object* v_tail_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_54_);
v_head_58_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_58_);
v_tail_59_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_59_);
lean_dec_ref(v_x_53_);
v___x_60_ = lean_apply_2(v_h__2_55_, v_head_58_, v_tail_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_motive_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(v_x_63_, v_h__1_64_, v_h__2_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_____do__lift_67_) == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__1_68_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_68_);
v_val_72_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_____do__lift_67_);
v___x_73_ = lean_apply_1(v_h__2_69_, v_val_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(lean_object* v_00_u03b2_74_, lean_object* v_motive_75_, lean_object* v_____do__lift_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(v_____do__lift_76_, v_h__1_77_, v_h__2_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__0(lean_object* v_z_80_, lean_object* v_toPure_81_, lean_object* v_zs_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v_z_80_);
lean_ctor_set(v___x_83_, 1, v_zs_82_);
v___x_84_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg(lean_object* v_inst_85_, lean_object* v_f_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_toBind_90_; lean_object* v_toPure_91_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_85_, 0);
v_toBind_90_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_90_);
v_toPure_91_ = lean_ctor_get(v_toApplicative_89_, 1);
lean_inc(v_toPure_91_);
if (lean_obj_tag(v_x_87_) == 1)
{
if (lean_obj_tag(v_x_88_) == 1)
{
lean_object* v_head_95_; lean_object* v_tail_96_; lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_head_95_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_95_);
v_tail_96_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_96_);
lean_dec_ref(v_x_87_);
v_head_97_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_x_88_);
lean_inc(v_toBind_90_);
lean_inc(v_f_86_);
v___f_99_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_99_, 0, v_toPure_91_);
lean_closure_set(v___f_99_, 1, v_inst_85_);
lean_closure_set(v___f_99_, 2, v_f_86_);
lean_closure_set(v___f_99_, 3, v_tail_96_);
lean_closure_set(v___f_99_, 4, v_tail_98_);
lean_closure_set(v___f_99_, 5, v_toBind_90_);
v___x_100_ = lean_apply_2(v_f_86_, v_head_95_, v_head_97_);
v___x_101_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v___x_100_, v___f_99_);
return v___x_101_;
}
else
{
lean_dec_ref(v_x_87_);
lean_dec(v_toBind_90_);
lean_dec(v_x_88_);
lean_dec(v_f_86_);
lean_dec_ref(v_inst_85_);
goto v___jp_92_;
}
}
else
{
lean_dec(v_toBind_90_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
lean_dec(v_f_86_);
lean_dec_ref(v_inst_85_);
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_2(v_toPure_91_, lean_box(0), v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__1(lean_object* v_toPure_102_, lean_object* v_inst_103_, lean_object* v_f_104_, lean_object* v_tail_105_, lean_object* v_tail_106_, lean_object* v_toBind_107_, lean_object* v_z_108_){
_start:
{
lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___f_109_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_109_, 0, v_z_108_);
lean_closure_set(v___f_109_, 1, v_toPure_102_);
v___x_110_ = l_List_zipWithM_x27___redArg(v_inst_103_, v_f_104_, v_tail_105_, v_tail_106_);
v___x_111_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v___x_110_, v___f_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27(lean_object* v_m_112_, lean_object* v_inst_113_, lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_00_u03b3_116_, lean_object* v_f_117_, lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_List_zipWithM_x27___redArg(v_inst_113_, v_f_117_, v_x_118_, v_x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_x_121_) == 1)
{
if (lean_obj_tag(v_x_122_) == 1)
{
lean_object* v_head_125_; lean_object* v_tail_126_; lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_124_);
v_head_125_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_head_125_);
v_tail_126_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_tail_126_);
lean_dec_ref(v_x_121_);
v_head_127_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_head_127_);
v_tail_128_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_tail_128_);
lean_dec_ref(v_x_122_);
v___x_129_ = lean_apply_4(v_h__1_123_, v_head_125_, v_tail_126_, v_head_127_, v_tail_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_dec(v_h__1_123_);
v___x_130_ = lean_apply_3(v_h__2_124_, v_x_121_, v_x_122_, lean_box(0));
return v___x_130_;
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v_h__1_123_);
v___x_131_ = lean_apply_3(v_h__2_124_, v_x_121_, v_x_122_, lean_box(0));
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_motive_134_, lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
if (lean_obj_tag(v_x_135_) == 1)
{
if (lean_obj_tag(v_x_136_) == 1)
{
lean_object* v_head_139_; lean_object* v_tail_140_; lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_138_);
v_head_139_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_head_139_);
v_tail_140_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_tail_140_);
lean_dec_ref(v_x_135_);
v_head_141_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_head_141_);
v_tail_142_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_tail_142_);
lean_dec_ref(v_x_136_);
v___x_143_ = lean_apply_4(v_h__1_137_, v_head_139_, v_tail_140_, v_head_141_, v_tail_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_h__1_137_);
v___x_144_ = lean_apply_3(v_h__2_138_, v_x_135_, v_x_136_, lean_box(0));
return v___x_144_;
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v_h__1_137_);
v___x_145_ = lean_apply_3(v_h__2_138_, v_x_135_, v_x_136_, lean_box(0));
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
if (lean_obj_tag(v_x_146_) == 1)
{
if (lean_obj_tag(v_x_147_) == 1)
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v_head_153_; lean_object* v_tail_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_150_);
v_head_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_tail_152_);
lean_dec_ref(v_x_146_);
v_head_153_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_head_153_);
v_tail_154_ = lean_ctor_get(v_x_147_, 1);
lean_inc(v_tail_154_);
lean_dec_ref(v_x_147_);
v___x_155_ = lean_apply_5(v_h__1_149_, v_head_151_, v_tail_152_, v_head_153_, v_tail_154_, v_x_148_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_h__1_149_);
v___x_156_ = lean_apply_4(v_h__2_150_, v_x_146_, v_x_147_, v_x_148_, lean_box(0));
return v___x_156_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v_h__1_149_);
v___x_157_ = lean_apply_4(v_h__2_150_, v_x_146_, v_x_147_, v_x_148_, lean_box(0));
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_00_u03b3_160_, lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_162_) == 1)
{
if (lean_obj_tag(v_x_163_) == 1)
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_166_);
v_head_167_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_head_167_);
v_tail_168_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_tail_168_);
lean_dec_ref(v_x_162_);
v_head_169_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_head_169_);
v_tail_170_ = lean_ctor_get(v_x_163_, 1);
lean_inc(v_tail_170_);
lean_dec_ref(v_x_163_);
v___x_171_ = lean_apply_5(v_h__1_165_, v_head_167_, v_tail_168_, v_head_169_, v_tail_170_, v_x_164_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
lean_dec(v_h__1_165_);
v___x_172_ = lean_apply_4(v_h__2_166_, v_x_162_, v_x_163_, v_x_164_, lean_box(0));
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v_h__1_165_);
v___x_173_ = lean_apply_4(v_h__2_166_, v_x_162_, v_x_163_, v_x_164_, lean_box(0));
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_178_; 
lean_dec(v_h__2_177_);
v___x_178_ = lean_apply_1(v_h__1_176_, v_x_175_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v_tail_180_; lean_object* v___x_181_; 
lean_dec(v_h__1_176_);
v_head_179_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_head_179_);
v_tail_180_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_tail_180_);
lean_dec_ref(v_x_174_);
v___x_181_ = lean_apply_3(v_h__2_177_, v_head_179_, v_tail_180_, v_x_175_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_motive_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(v_x_185_, v_x_186_, v_h__1_187_, v_h__2_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
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
lean_dec_ref(v_x_190_);
v___x_196_ = lean_apply_1(v_h__2_192_, v_val_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_197_, lean_object* v_motive_198_, lean_object* v_x_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(v_x_199_, v_h__1_200_, v_h__2_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object* v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_h__1_204_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_apply_1(v_h__2_205_, v___x_206_);
return v___x_207_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_205_);
v_val_208_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_val_208_);
lean_dec_ref(v_x_203_);
v___x_209_ = lean_apply_1(v_h__1_204_, v_val_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object* v_00_u03b2_210_, lean_object* v_motive_211_, lean_object* v_x_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(v_x_212_, v_h__1_213_, v_h__2_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_220_; 
lean_dec(v_h__2_219_);
v___x_220_ = lean_apply_2(v_h__1_218_, v_x_217_, lean_box(0));
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_223_; 
lean_dec(v_h__1_218_);
v_head_221_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_head_221_);
v_tail_222_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_tail_222_);
lean_dec_ref(v_x_216_);
v___x_223_ = lean_apply_4(v_h__2_219_, v_head_221_, v_tail_222_, v_x_217_, lean_box(0));
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_as_226_, lean_object* v_motive_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(v_x_228_, v_x_229_, v_h__1_231_, v_h__2_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___boxed(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_as_236_, lean_object* v_motive_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(v_00_u03b1_234_, v_00_u03b2_235_, v_as_236_, v_motive_237_, v_x_238_, v_x_239_, v_x_240_, v_h__1_241_, v_h__2_242_);
lean_dec(v_as_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_____do__lift_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_){
_start:
{
if (lean_obj_tag(v_____do__lift_244_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec(v_h__2_246_);
v_a_247_ = lean_ctor_get(v_____do__lift_244_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v_____do__lift_244_);
v___x_248_ = lean_apply_1(v_h__1_245_, v_a_247_);
return v___x_248_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_250_; 
lean_dec(v_h__1_245_);
v_a_249_ = lean_ctor_get(v_____do__lift_244_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v_____do__lift_244_);
v___x_250_ = lean_apply_1(v_h__2_246_, v_a_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b2_251_, lean_object* v_motive_252_, lean_object* v_____do__lift_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(v_____do__lift_253_, v_h__1_254_, v_h__2_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; 
lean_dec(v_h__2_259_);
v_a_260_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_a_260_);
lean_dec_ref(v_x_257_);
v___x_261_ = lean_apply_1(v_h__1_258_, v_a_260_);
return v___x_261_;
}
else
{
lean_object* v_a_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_258_);
v_a_262_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v_x_257_);
v___x_263_ = lean_apply_1(v_h__2_259_, v_a_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_264_, lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_266_, v_h__1_267_, v_h__2_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
if (lean_obj_tag(v_b_270_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; 
lean_dec(v_h__1_271_);
v_a_273_ = lean_ctor_get(v_b_270_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v_b_270_);
v___x_274_ = lean_apply_1(v_h__2_272_, v_a_273_);
return v___x_274_;
}
else
{
lean_object* v_a_275_; lean_object* v___x_276_; 
lean_dec(v_h__2_272_);
v_a_275_ = lean_ctor_get(v_b_270_, 0);
lean_inc(v_a_275_);
lean_dec_ref(v_b_270_);
v___x_276_ = lean_apply_1(v_h__1_271_, v_a_275_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_277_, lean_object* v_motive_278_, lean_object* v_b_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(v_b_279_, v_h__1_280_, v_h__2_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_h__2_285_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_apply_1(v_h__1_284_, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_tail_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_284_);
v_head_288_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_head_288_);
v_tail_289_ = lean_ctor_get(v_x_283_, 1);
lean_inc(v_tail_289_);
lean_dec_ref(v_x_283_);
v___x_290_ = lean_apply_2(v_h__2_285_, v_head_288_, v_tail_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_291_, lean_object* v_motive_292_, lean_object* v_x_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(v_x_293_, v_h__1_294_, v_h__2_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_){
_start:
{
if (v_____do__lift_297_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__1_298_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__2_299_, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_h__2_299_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v_h__1_298_, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
uint8_t v_____do__lift_22__boxed_307_; lean_object* v_res_308_; 
v_____do__lift_22__boxed_307_ = lean_unbox(v_____do__lift_304_);
v_res_308_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(v_____do__lift_22__boxed_307_, v_h__1_305_, v_h__2_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(lean_object* v_motive_309_, uint8_t v_____do__lift_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(v_____do__lift_310_, v_h__1_311_, v_h__2_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_314_, lean_object* v_____do__lift_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
uint8_t v_____do__lift_33__boxed_318_; lean_object* v_res_319_; 
v_____do__lift_33__boxed_318_ = lean_unbox(v_____do__lift_315_);
v_res_319_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(v_motive_314_, v_____do__lift_33__boxed_318_, v_h__1_316_, v_h__2_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_){
_start:
{
if (lean_obj_tag(v_____do__lift_320_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_h__2_322_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_1(v_h__1_321_, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v_val_325_; lean_object* v___x_326_; 
lean_dec(v_h__1_321_);
v_val_325_ = lean_ctor_get(v_____do__lift_320_, 0);
lean_inc(v_val_325_);
lean_dec_ref(v_____do__lift_320_);
v___x_326_ = lean_apply_1(v_h__2_322_, v_val_325_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_327_, lean_object* v_motive_328_, lean_object* v_____do__lift_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(v_____do__lift_329_, v_h__1_330_, v_h__2_331_);
return v___x_332_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Monadic(builtin);
}
#ifdef __cplusplus
}
#endif
