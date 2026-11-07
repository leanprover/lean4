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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_toBind_14_, 2);
v_toPure_15_ = lean_ctor_get(v_toApplicative_13_, 1);
lean_inc(v_toPure_15_);
v_head_16_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_x_8_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_____do__lift_37_) == 0)
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
v_val_42_ = lean_ctor_get(v_____do__lift_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v_____do__lift_37_, 1);
v___x_43_ = lean_apply_1(v_h__2_39_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_____do__lift_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_____do__lift_46_) == 0)
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
v_val_51_ = lean_ctor_get(v_____do__lift_46_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_____do__lift_46_, 1);
v___x_52_ = lean_apply_1(v_h__2_48_, v_val_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_57_; 
lean_dec(v_h__2_56_);
v___x_57_ = lean_apply_1(v_h__1_55_, v_x_54_);
return v___x_57_;
}
else
{
lean_object* v_head_58_; lean_object* v_tail_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_55_);
v_head_58_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_58_);
v_tail_59_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_59_);
lean_dec_ref_known(v_x_53_, 2);
v___x_60_ = lean_apply_3(v_h__2_56_, v_head_58_, v_tail_59_, v_x_54_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_object* v___x_68_; 
lean_dec(v_h__2_67_);
v___x_68_ = lean_apply_1(v_h__1_66_, v_x_65_);
return v___x_68_;
}
else
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_66_);
v_head_69_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_64_, 2);
v___x_71_ = lean_apply_3(v_h__2_67_, v_head_69_, v_tail_70_, v_x_65_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__0(lean_object* v_z_72_, lean_object* v_toPure_73_, lean_object* v_zs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_z_72_);
lean_ctor_set(v___x_75_, 1, v_zs_74_);
v___x_76_ = lean_apply_2(v_toPure_73_, lean_box(0), v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg(lean_object* v_inst_77_, lean_object* v_f_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toBind_82_; lean_object* v_toPure_83_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_77_, 0);
v_toBind_82_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_toBind_82_);
v_toPure_83_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc(v_toPure_83_);
if (lean_obj_tag(v_x_79_) == 1)
{
if (lean_obj_tag(v_x_80_) == 1)
{
lean_object* v_head_87_; lean_object* v_tail_88_; lean_object* v_head_89_; lean_object* v_tail_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_head_87_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_head_87_);
v_tail_88_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_tail_88_);
lean_dec_ref_known(v_x_79_, 2);
v_head_89_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_head_89_);
v_tail_90_ = lean_ctor_get(v_x_80_, 1);
lean_inc(v_tail_90_);
lean_dec_ref_known(v_x_80_, 2);
lean_inc(v_toBind_82_);
lean_inc(v_f_78_);
v___f_91_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_91_, 0, v_toPure_83_);
lean_closure_set(v___f_91_, 1, v_inst_77_);
lean_closure_set(v___f_91_, 2, v_f_78_);
lean_closure_set(v___f_91_, 3, v_tail_88_);
lean_closure_set(v___f_91_, 4, v_tail_90_);
lean_closure_set(v___f_91_, 5, v_toBind_82_);
v___x_92_ = lean_apply_2(v_f_78_, v_head_87_, v_head_89_);
v___x_93_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
else
{
lean_dec_ref_known(v_x_79_, 2);
lean_dec(v_toBind_82_);
lean_dec(v_x_80_);
lean_dec(v_f_78_);
lean_dec_ref(v_inst_77_);
goto v___jp_84_;
}
}
else
{
lean_dec(v_toBind_82_);
lean_dec(v_x_80_);
lean_dec(v_x_79_);
lean_dec(v_f_78_);
lean_dec_ref(v_inst_77_);
goto v___jp_84_;
}
v___jp_84_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__1(lean_object* v_toPure_94_, lean_object* v_inst_95_, lean_object* v_f_96_, lean_object* v_tail_97_, lean_object* v_tail_98_, lean_object* v_toBind_99_, lean_object* v_z_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___f_101_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_101_, 0, v_z_100_);
lean_closure_set(v___f_101_, 1, v_toPure_94_);
v___x_102_ = l_List_zipWithM_x27___redArg(v_inst_95_, v_f_96_, v_tail_97_, v_tail_98_);
v___x_103_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_102_, v___f_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27(lean_object* v_m_104_, lean_object* v_inst_105_, lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_00_u03b3_108_, lean_object* v_f_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_List_zipWithM_x27___redArg(v_inst_105_, v_f_109_, v_x_110_, v_x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_113_) == 1)
{
if (lean_obj_tag(v_x_114_) == 1)
{
lean_object* v_head_117_; lean_object* v_tail_118_; lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_116_);
v_head_117_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_head_117_);
v_tail_118_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_tail_118_);
lean_dec_ref_known(v_x_113_, 2);
v_head_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_head_119_);
v_tail_120_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_tail_120_);
lean_dec_ref_known(v_x_114_, 2);
v___x_121_ = lean_apply_4(v_h__1_115_, v_head_117_, v_tail_118_, v_head_119_, v_tail_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_h__1_115_);
v___x_122_ = lean_apply_3(v_h__2_116_, v_x_113_, v_x_114_, lean_box(0));
return v___x_122_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec(v_h__1_115_);
v___x_123_ = lean_apply_3(v_h__2_116_, v_x_113_, v_x_114_, lean_box(0));
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_127_) == 1)
{
if (lean_obj_tag(v_x_128_) == 1)
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_130_);
v_head_131_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_head_131_);
v_tail_132_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_tail_132_);
lean_dec_ref_known(v_x_127_, 2);
v_head_133_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_133_);
v_tail_134_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_134_);
lean_dec_ref_known(v_x_128_, 2);
v___x_135_ = lean_apply_4(v_h__1_129_, v_head_131_, v_tail_132_, v_head_133_, v_tail_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
lean_dec(v_h__1_129_);
v___x_136_ = lean_apply_3(v_h__2_130_, v_x_127_, v_x_128_, lean_box(0));
return v___x_136_;
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v_h__1_129_);
v___x_137_ = lean_apply_3(v_h__2_130_, v_x_127_, v_x_128_, lean_box(0));
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
if (lean_obj_tag(v_x_138_) == 1)
{
if (lean_obj_tag(v_x_139_) == 1)
{
lean_object* v_head_143_; lean_object* v_tail_144_; lean_object* v_head_145_; lean_object* v_tail_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_142_);
v_head_143_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_head_143_);
v_tail_144_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_tail_144_);
lean_dec_ref_known(v_x_138_, 2);
v_head_145_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_head_145_);
v_tail_146_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_tail_146_);
lean_dec_ref_known(v_x_139_, 2);
v___x_147_ = lean_apply_5(v_h__1_141_, v_head_143_, v_tail_144_, v_head_145_, v_tail_146_, v_x_140_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; 
lean_dec(v_h__1_141_);
v___x_148_ = lean_apply_4(v_h__2_142_, v_x_138_, v_x_139_, v_x_140_, lean_box(0));
return v___x_148_;
}
}
else
{
lean_object* v___x_149_; 
lean_dec(v_h__1_141_);
v___x_149_ = lean_apply_4(v_h__2_142_, v_x_138_, v_x_139_, v_x_140_, lean_box(0));
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_00_u03b3_152_, lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_){
_start:
{
if (lean_obj_tag(v_x_154_) == 1)
{
if (lean_obj_tag(v_x_155_) == 1)
{
lean_object* v_head_159_; lean_object* v_tail_160_; lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v___x_163_; 
lean_dec(v_h__2_158_);
v_head_159_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_head_159_);
v_tail_160_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_tail_160_);
lean_dec_ref_known(v_x_154_, 2);
v_head_161_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_head_161_);
v_tail_162_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_tail_162_);
lean_dec_ref_known(v_x_155_, 2);
v___x_163_ = lean_apply_5(v_h__1_157_, v_head_159_, v_tail_160_, v_head_161_, v_tail_162_, v_x_156_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
lean_dec(v_h__1_157_);
v___x_164_ = lean_apply_4(v_h__2_158_, v_x_154_, v_x_155_, v_x_156_, lean_box(0));
return v___x_164_;
}
}
else
{
lean_object* v___x_165_; 
lean_dec(v_h__1_157_);
v___x_165_ = lean_apply_4(v_h__2_158_, v_x_154_, v_x_155_, v_x_156_, lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_170_; 
lean_dec(v_h__2_169_);
v___x_170_ = lean_apply_1(v_h__1_168_, v_x_167_);
return v___x_170_;
}
else
{
lean_object* v_head_171_; lean_object* v_tail_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_168_);
v_head_171_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_head_171_);
v_tail_172_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_tail_172_);
lean_dec_ref_known(v_x_166_, 2);
v___x_173_ = lean_apply_3(v_h__2_169_, v_head_171_, v_tail_172_, v_x_167_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_motive_176_, lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_181_; 
lean_dec(v_h__2_180_);
v___x_181_ = lean_apply_1(v_h__1_179_, v_x_178_);
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_184_; 
lean_dec(v_h__1_179_);
v_head_182_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_head_182_);
v_tail_183_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_tail_183_);
lean_dec_ref_known(v_x_177_, 2);
v___x_184_ = lean_apply_3(v_h__2_180_, v_head_182_, v_tail_183_, v_x_178_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_h__2_187_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_h__1_186_, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v_val_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_186_);
v_val_190_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_x_185_, 1);
v___x_191_ = lean_apply_1(v_h__2_187_, v_val_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_192_, lean_object* v_motive_193_, lean_object* v_x_194_, lean_object* v_h__1_195_, lean_object* v_h__2_196_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__2_196_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__1_195_, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_200_; 
lean_dec(v_h__1_195_);
v_val_199_ = lean_ctor_get(v_x_194_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v_x_194_, 1);
v___x_200_ = lean_apply_1(v_h__2_196_, v_val_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__1_202_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v_h__2_203_, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; 
lean_dec(v_h__2_203_);
v_val_206_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v_x_201_, 1);
v___x_207_ = lean_apply_1(v_h__1_202_, v_val_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object* v_00_u03b2_208_, lean_object* v_motive_209_, lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_211_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__2_212_, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
lean_dec(v_h__2_212_);
v_val_215_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v_x_210_, 1);
v___x_216_ = lean_apply_1(v_h__1_211_, v_val_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_____do__lift_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
if (lean_obj_tag(v_____do__lift_217_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_219_);
v_a_220_ = lean_ctor_get(v_____do__lift_217_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v_____do__lift_217_, 1);
v___x_221_ = lean_apply_1(v_h__1_218_, v_a_220_);
return v___x_221_;
}
else
{
lean_object* v_a_222_; lean_object* v___x_223_; 
lean_dec(v_h__1_218_);
v_a_222_ = lean_ctor_get(v_____do__lift_217_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v_____do__lift_217_, 1);
v___x_223_ = lean_apply_1(v_h__2_219_, v_a_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b2_224_, lean_object* v_motive_225_, lean_object* v_____do__lift_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
if (lean_obj_tag(v_____do__lift_226_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
lean_dec(v_h__2_228_);
v_a_229_ = lean_ctor_get(v_____do__lift_226_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v_____do__lift_226_, 1);
v___x_230_ = lean_apply_1(v_h__1_227_, v_a_229_);
return v___x_230_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_227_);
v_a_231_ = lean_ctor_get(v_____do__lift_226_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v_____do__lift_226_, 1);
v___x_232_ = lean_apply_1(v_h__2_228_, v_a_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
lean_dec(v_h__2_235_);
v_a_236_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v_x_233_, 1);
v___x_237_ = lean_apply_1(v_h__1_234_, v_a_236_);
return v___x_237_;
}
else
{
lean_object* v_a_238_; lean_object* v___x_239_; 
lean_dec(v_h__1_234_);
v_a_238_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v_x_233_, 1);
v___x_239_ = lean_apply_1(v_h__2_235_, v_a_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; 
lean_dec(v_h__2_244_);
v_a_245_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v_x_242_, 1);
v___x_246_ = lean_apply_1(v_h__1_243_, v_a_245_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_243_);
v_a_247_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v_x_242_, 1);
v___x_248_ = lean_apply_1(v_h__2_244_, v_a_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
if (lean_obj_tag(v_b_249_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; 
lean_dec(v_h__1_250_);
v_a_252_ = lean_ctor_get(v_b_249_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v_b_249_, 1);
v___x_253_ = lean_apply_1(v_h__2_251_, v_a_252_);
return v___x_253_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_255_; 
lean_dec(v_h__2_251_);
v_a_254_ = lean_ctor_get(v_b_249_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v_b_249_, 1);
v___x_255_ = lean_apply_1(v_h__1_250_, v_a_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_256_, lean_object* v_motive_257_, lean_object* v_b_258_, lean_object* v_h__1_259_, lean_object* v_h__2_260_){
_start:
{
if (lean_obj_tag(v_b_258_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_259_);
v_a_261_ = lean_ctor_get(v_b_258_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_b_258_, 1);
v___x_262_ = lean_apply_1(v_h__2_260_, v_a_261_);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; 
lean_dec(v_h__2_260_);
v_a_263_ = lean_ctor_get(v_b_258_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_b_258_, 1);
v___x_264_ = lean_apply_1(v_h__1_259_, v_a_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (v_____do__lift_265_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_h__1_266_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_1(v_h__2_267_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_h__2_267_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_h__1_266_, v___x_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_){
_start:
{
uint8_t v_____do__lift_24__boxed_275_; lean_object* v_res_276_; 
v_____do__lift_24__boxed_275_ = lean_unbox(v_____do__lift_272_);
v_res_276_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_275_, v_h__1_273_, v_h__2_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(lean_object* v_motive_277_, uint8_t v_____do__lift_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
if (v_____do__lift_278_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_h__1_279_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_apply_1(v_h__2_280_, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_h__2_280_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_1(v_h__1_279_, v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_285_, lean_object* v_____do__lift_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
uint8_t v_____do__lift_35__boxed_289_; lean_object* v_res_290_; 
v_____do__lift_35__boxed_289_ = lean_unbox(v_____do__lift_286_);
v_res_290_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(v_motive_285_, v_____do__lift_35__boxed_289_, v_h__1_287_, v_h__2_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
if (lean_obj_tag(v_____do__lift_291_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_h__2_293_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_apply_1(v_h__1_292_, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_292_);
v_val_296_ = lean_ctor_get(v_____do__lift_291_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v_____do__lift_291_, 1);
v___x_297_ = lean_apply_1(v_h__2_293_, v_val_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_298_, lean_object* v_motive_299_, lean_object* v_____do__lift_300_, lean_object* v_h__1_301_, lean_object* v_h__2_302_){
_start:
{
if (lean_obj_tag(v_____do__lift_300_) == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_h__2_302_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_h__1_301_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_306_; 
lean_dec(v_h__1_301_);
v_val_305_ = lean_ctor_get(v_____do__lift_300_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_____do__lift_300_, 1);
v___x_306_ = lean_apply_1(v_h__2_302_, v_val_305_);
return v___x_306_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
