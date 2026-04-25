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
lean_inc_n(v_toBind_14_, 2);
v_toPure_15_ = lean_ctor_get(v_toApplicative_13_, 1);
lean_inc(v_toPure_15_);
v_head_16_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_tail_17_);
lean_dec_ref(v_x_8_);
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
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v___x_52_; 
lean_dec(v_h__2_51_);
v___x_52_ = lean_apply_1(v_h__1_50_, v_x_49_);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_50_);
v_head_53_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_x_48_, 1);
lean_inc(v_tail_54_);
lean_dec_ref(v_x_48_);
v___x_55_ = lean_apply_3(v_h__2_51_, v_head_53_, v_tail_54_, v_x_49_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_57_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_head_61_; lean_object* v_tail_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_57_);
v_head_61_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_head_61_);
v_tail_62_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_tail_62_);
lean_dec_ref(v_x_56_);
v___x_63_ = lean_apply_2(v_h__2_58_, v_head_61_, v_tail_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter(lean_object* v_00_u03b1_64_, lean_object* v_motive_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_68_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_67_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_67_);
v_head_71_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_head_71_);
v_tail_72_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_tail_72_);
lean_dec_ref(v_x_66_);
v___x_73_ = lean_apply_2(v_h__2_68_, v_head_71_, v_tail_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
if (lean_obj_tag(v_____do__lift_74_) == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_76_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__1_75_, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v_val_79_; lean_object* v___x_80_; 
lean_dec(v_h__1_75_);
v_val_79_ = lean_ctor_get(v_____do__lift_74_, 0);
lean_inc(v_val_79_);
lean_dec_ref(v_____do__lift_74_);
v___x_80_ = lean_apply_1(v_h__2_76_, v_val_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(lean_object* v_00_u03b2_81_, lean_object* v_motive_82_, lean_object* v_____do__lift_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
if (lean_obj_tag(v_____do__lift_83_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_85_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__1_84_, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_89_; 
lean_dec(v_h__1_84_);
v_val_88_ = lean_ctor_get(v_____do__lift_83_, 0);
lean_inc(v_val_88_);
lean_dec_ref(v_____do__lift_83_);
v___x_89_ = lean_apply_1(v_h__2_85_, v_val_88_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__0(lean_object* v_z_90_, lean_object* v_toPure_91_, lean_object* v_zs_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v_z_90_);
lean_ctor_set(v___x_93_, 1, v_zs_92_);
v___x_94_ = lean_apply_2(v_toPure_91_, lean_box(0), v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg(lean_object* v_inst_95_, lean_object* v_f_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_toApplicative_99_; lean_object* v_toBind_100_; lean_object* v_toPure_101_; 
v_toApplicative_99_ = lean_ctor_get(v_inst_95_, 0);
v_toBind_100_ = lean_ctor_get(v_inst_95_, 1);
lean_inc(v_toBind_100_);
v_toPure_101_ = lean_ctor_get(v_toApplicative_99_, 1);
lean_inc(v_toPure_101_);
if (lean_obj_tag(v_x_97_) == 1)
{
if (lean_obj_tag(v_x_98_) == 1)
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v_head_107_; lean_object* v_tail_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_head_105_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_head_105_);
v_tail_106_ = lean_ctor_get(v_x_97_, 1);
lean_inc(v_tail_106_);
lean_dec_ref(v_x_97_);
v_head_107_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_107_);
v_tail_108_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_tail_108_);
lean_dec_ref(v_x_98_);
lean_inc(v_toBind_100_);
lean_inc(v_f_96_);
v___f_109_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_109_, 0, v_toPure_101_);
lean_closure_set(v___f_109_, 1, v_inst_95_);
lean_closure_set(v___f_109_, 2, v_f_96_);
lean_closure_set(v___f_109_, 3, v_tail_106_);
lean_closure_set(v___f_109_, 4, v_tail_108_);
lean_closure_set(v___f_109_, 5, v_toBind_100_);
v___x_110_ = lean_apply_2(v_f_96_, v_head_105_, v_head_107_);
v___x_111_ = lean_apply_4(v_toBind_100_, lean_box(0), lean_box(0), v___x_110_, v___f_109_);
return v___x_111_;
}
else
{
lean_dec_ref(v_x_97_);
lean_dec(v_toBind_100_);
lean_dec(v_x_98_);
lean_dec(v_f_96_);
lean_dec_ref(v_inst_95_);
goto v___jp_102_;
}
}
else
{
lean_dec(v_toBind_100_);
lean_dec(v_x_98_);
lean_dec(v_x_97_);
lean_dec(v_f_96_);
lean_dec_ref(v_inst_95_);
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_2(v_toPure_101_, lean_box(0), v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27___redArg___lam__1(lean_object* v_toPure_112_, lean_object* v_inst_113_, lean_object* v_f_114_, lean_object* v_tail_115_, lean_object* v_tail_116_, lean_object* v_toBind_117_, lean_object* v_z_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___f_119_ = lean_alloc_closure((void*)(l_List_zipWithM_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_119_, 0, v_z_118_);
lean_closure_set(v___f_119_, 1, v_toPure_112_);
v___x_120_ = l_List_zipWithM_x27___redArg(v_inst_113_, v_f_114_, v_tail_115_, v_tail_116_);
v___x_121_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_120_, v___f_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_x27(lean_object* v_m_122_, lean_object* v_inst_123_, lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_00_u03b3_126_, lean_object* v_f_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_List_zipWithM_x27___redArg(v_inst_123_, v_f_127_, v_x_128_, v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_131_) == 1)
{
if (lean_obj_tag(v_x_132_) == 1)
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_139_; 
lean_dec(v_h__2_134_);
v_head_135_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_head_135_);
v_tail_136_ = lean_ctor_get(v_x_131_, 1);
lean_inc(v_tail_136_);
lean_dec_ref(v_x_131_);
v_head_137_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_head_137_);
v_tail_138_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_tail_138_);
lean_dec_ref(v_x_132_);
v___x_139_ = lean_apply_4(v_h__1_133_, v_head_135_, v_tail_136_, v_head_137_, v_tail_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; 
lean_dec(v_h__1_133_);
v___x_140_ = lean_apply_3(v_h__2_134_, v_x_131_, v_x_132_, lean_box(0));
return v___x_140_;
}
}
else
{
lean_object* v___x_141_; 
lean_dec(v_h__1_133_);
v___x_141_ = lean_apply_3(v_h__2_134_, v_x_131_, v_x_132_, lean_box(0));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
if (lean_obj_tag(v_x_145_) == 1)
{
if (lean_obj_tag(v_x_146_) == 1)
{
lean_object* v_head_149_; lean_object* v_tail_150_; lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_148_);
v_head_149_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_head_149_);
v_tail_150_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_tail_150_);
lean_dec_ref(v_x_145_);
v_head_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_tail_152_);
lean_dec_ref(v_x_146_);
v___x_153_ = lean_apply_4(v_h__1_147_, v_head_149_, v_tail_150_, v_head_151_, v_tail_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
lean_dec(v_h__1_147_);
v___x_154_ = lean_apply_3(v_h__2_148_, v_x_145_, v_x_146_, lean_box(0));
return v___x_154_;
}
}
else
{
lean_object* v___x_155_; 
lean_dec(v_h__1_147_);
v___x_155_ = lean_apply_3(v_h__2_148_, v_x_145_, v_x_146_, lean_box(0));
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_){
_start:
{
if (lean_obj_tag(v_x_156_) == 1)
{
if (lean_obj_tag(v_x_157_) == 1)
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v_head_163_; lean_object* v_tail_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_160_);
v_head_161_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_161_);
v_tail_162_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_tail_162_);
lean_dec_ref(v_x_156_);
v_head_163_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_163_);
v_tail_164_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_tail_164_);
lean_dec_ref(v_x_157_);
v___x_165_ = lean_apply_5(v_h__1_159_, v_head_161_, v_tail_162_, v_head_163_, v_tail_164_, v_x_158_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
lean_dec(v_h__1_159_);
v___x_166_ = lean_apply_4(v_h__2_160_, v_x_156_, v_x_157_, v_x_158_, lean_box(0));
return v___x_166_;
}
}
else
{
lean_object* v___x_167_; 
lean_dec(v_h__1_159_);
v___x_167_ = lean_apply_4(v_h__2_160_, v_x_156_, v_x_157_, v_x_158_, lean_box(0));
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_00_u03b3_170_, lean_object* v_motive_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (lean_obj_tag(v_x_172_) == 1)
{
if (lean_obj_tag(v_x_173_) == 1)
{
lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v_head_179_; lean_object* v_tail_180_; lean_object* v___x_181_; 
lean_dec(v_h__2_176_);
v_head_177_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_head_177_);
v_tail_178_ = lean_ctor_get(v_x_172_, 1);
lean_inc(v_tail_178_);
lean_dec_ref(v_x_172_);
v_head_179_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_179_);
v_tail_180_ = lean_ctor_get(v_x_173_, 1);
lean_inc(v_tail_180_);
lean_dec_ref(v_x_173_);
v___x_181_ = lean_apply_5(v_h__1_175_, v_head_177_, v_tail_178_, v_head_179_, v_tail_180_, v_x_174_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
lean_dec(v_h__1_175_);
v___x_182_ = lean_apply_4(v_h__2_176_, v_x_172_, v_x_173_, v_x_174_, lean_box(0));
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_h__1_175_);
v___x_183_ = lean_apply_4(v_h__2_176_, v_x_172_, v_x_173_, v_x_174_, lean_box(0));
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_188_; 
lean_dec(v_h__2_187_);
v___x_188_ = lean_apply_1(v_h__1_186_, v_x_185_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_186_);
v_head_189_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_head_189_);
v_tail_190_ = lean_ctor_get(v_x_184_, 1);
lean_inc(v_tail_190_);
lean_dec_ref(v_x_184_);
v___x_191_ = lean_apply_3(v_h__2_187_, v_head_189_, v_tail_190_, v_x_185_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_motive_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v___x_199_; 
lean_dec(v_h__2_198_);
v___x_199_ = lean_apply_1(v_h__1_197_, v_x_196_);
return v___x_199_;
}
else
{
lean_object* v_head_200_; lean_object* v_tail_201_; lean_object* v___x_202_; 
lean_dec(v_h__1_197_);
v_head_200_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_head_200_);
v_tail_201_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_tail_201_);
lean_dec_ref(v_x_195_);
v___x_202_ = lean_apply_3(v_h__2_198_, v_head_200_, v_tail_201_, v_x_196_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_h__2_205_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_apply_1(v_h__1_204_, v___x_206_);
return v___x_207_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_209_; 
lean_dec(v_h__1_204_);
v_val_208_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_val_208_);
lean_dec_ref(v_x_203_);
v___x_209_ = lean_apply_1(v_h__2_205_, v_val_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_210_, lean_object* v_motive_211_, lean_object* v_x_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_h__2_214_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v_h__1_213_, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; 
lean_dec(v_h__1_213_);
v_val_217_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v_x_212_);
v___x_218_ = lean_apply_1(v_h__2_214_, v_val_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object* v_x_219_, lean_object* v_h__1_220_, lean_object* v_h__2_221_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v_h__1_220_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_apply_1(v_h__2_221_, v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; 
lean_dec(v_h__2_221_);
v_val_224_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_val_224_);
lean_dec_ref(v_x_219_);
v___x_225_ = lean_apply_1(v_h__1_220_, v_val_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object* v_00_u03b2_226_, lean_object* v_motive_227_, lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__2_230_, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
lean_dec(v_h__2_230_);
v_val_233_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v_x_228_);
v___x_234_ = lean_apply_1(v_h__1_229_, v_val_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_239_; 
lean_dec(v_h__2_238_);
v___x_239_ = lean_apply_2(v_h__1_237_, v_x_236_, lean_box(0));
return v___x_239_;
}
else
{
lean_object* v_head_240_; lean_object* v_tail_241_; lean_object* v___x_242_; 
lean_dec(v_h__1_237_);
v_head_240_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_head_240_);
v_tail_241_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_tail_241_);
lean_dec_ref(v_x_235_);
v___x_242_ = lean_apply_4(v_h__2_238_, v_head_240_, v_tail_241_, v_x_236_, lean_box(0));
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_as_245_, lean_object* v_motive_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v___x_252_; 
lean_dec(v_h__2_251_);
v___x_252_ = lean_apply_2(v_h__1_250_, v_x_248_, lean_box(0));
return v___x_252_;
}
else
{
lean_object* v_head_253_; lean_object* v_tail_254_; lean_object* v___x_255_; 
lean_dec(v_h__1_250_);
v_head_253_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_head_253_);
v_tail_254_ = lean_ctor_get(v_x_247_, 1);
lean_inc(v_tail_254_);
lean_dec_ref(v_x_247_);
v___x_255_ = lean_apply_4(v_h__2_251_, v_head_253_, v_tail_254_, v_x_248_, lean_box(0));
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_as_258_, lean_object* v_motive_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(v_00_u03b1_256_, v_00_u03b2_257_, v_as_258_, v_motive_259_, v_x_260_, v_x_261_, v_x_262_, v_h__1_263_, v_h__2_264_);
lean_dec(v_as_258_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_____do__lift_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
if (lean_obj_tag(v_____do__lift_266_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; 
lean_dec(v_h__2_268_);
v_a_269_ = lean_ctor_get(v_____do__lift_266_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v_____do__lift_266_);
v___x_270_ = lean_apply_1(v_h__1_267_, v_a_269_);
return v___x_270_;
}
else
{
lean_object* v_a_271_; lean_object* v___x_272_; 
lean_dec(v_h__1_267_);
v_a_271_ = lean_ctor_get(v_____do__lift_266_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v_____do__lift_266_);
v___x_272_ = lean_apply_1(v_h__2_268_, v_a_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b2_273_, lean_object* v_motive_274_, lean_object* v_____do__lift_275_, lean_object* v_h__1_276_, lean_object* v_h__2_277_){
_start:
{
if (lean_obj_tag(v_____do__lift_275_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; 
lean_dec(v_h__2_277_);
v_a_278_ = lean_ctor_get(v_____do__lift_275_, 0);
lean_inc(v_a_278_);
lean_dec_ref(v_____do__lift_275_);
v___x_279_ = lean_apply_1(v_h__1_276_, v_a_278_);
return v___x_279_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_281_; 
lean_dec(v_h__1_276_);
v_a_280_ = lean_ctor_get(v_____do__lift_275_, 0);
lean_inc(v_a_280_);
lean_dec_ref(v_____do__lift_275_);
v___x_281_ = lean_apply_1(v_h__2_277_, v_a_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_284_);
v_a_285_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v_x_282_);
v___x_286_ = lean_apply_1(v_h__1_283_, v_a_285_);
return v___x_286_;
}
else
{
lean_object* v_a_287_; lean_object* v___x_288_; 
lean_dec(v_h__1_283_);
v_a_287_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_a_287_);
lean_dec_ref(v_x_282_);
v___x_288_ = lean_apply_1(v_h__2_284_, v_a_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_289_, lean_object* v_motive_290_, lean_object* v_x_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
lean_dec(v_h__2_293_);
v_a_294_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v_x_291_);
v___x_295_ = lean_apply_1(v_h__1_292_, v_a_294_);
return v___x_295_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_292_);
v_a_296_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v_x_291_);
v___x_297_ = lean_apply_1(v_h__2_293_, v_a_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
if (lean_obj_tag(v_b_298_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; 
lean_dec(v_h__1_299_);
v_a_301_ = lean_ctor_get(v_b_298_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v_b_298_);
v___x_302_ = lean_apply_1(v_h__2_300_, v_a_301_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_304_; 
lean_dec(v_h__2_300_);
v_a_303_ = lean_ctor_get(v_b_298_, 0);
lean_inc(v_a_303_);
lean_dec_ref(v_b_298_);
v___x_304_ = lean_apply_1(v_h__1_299_, v_a_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_305_, lean_object* v_motive_306_, lean_object* v_b_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_){
_start:
{
if (lean_obj_tag(v_b_307_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_308_);
v_a_310_ = lean_ctor_get(v_b_307_, 0);
lean_inc(v_a_310_);
lean_dec_ref(v_b_307_);
v___x_311_ = lean_apply_1(v_h__2_309_, v_a_310_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_313_; 
lean_dec(v_h__2_309_);
v_a_312_ = lean_ctor_get(v_b_307_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v_b_307_);
v___x_313_ = lean_apply_1(v_h__1_308_, v_a_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_h__2_316_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_1(v_h__1_315_, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v_head_319_; lean_object* v_tail_320_; lean_object* v___x_321_; 
lean_dec(v_h__1_315_);
v_head_319_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_head_319_);
v_tail_320_ = lean_ctor_get(v_x_314_, 1);
lean_inc(v_tail_320_);
lean_dec_ref(v_x_314_);
v___x_321_ = lean_apply_2(v_h__2_316_, v_head_319_, v_tail_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_322_, lean_object* v_motive_323_, lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_h__2_326_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_h__1_325_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_325_);
v_head_329_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_head_329_);
v_tail_330_ = lean_ctor_get(v_x_324_, 1);
lean_inc(v_tail_330_);
lean_dec_ref(v_x_324_);
v___x_331_ = lean_apply_2(v_h__2_326_, v_head_329_, v_tail_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
if (v_____do__lift_332_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_h__1_333_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_1(v_h__2_334_, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__2_334_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__1_333_, v___x_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
uint8_t v_____do__lift_26__boxed_342_; lean_object* v_res_343_; 
v_____do__lift_26__boxed_342_ = lean_unbox(v_____do__lift_339_);
v_res_343_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(v_____do__lift_26__boxed_342_, v_h__1_340_, v_h__2_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(lean_object* v_motive_344_, uint8_t v_____do__lift_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_){
_start:
{
if (v_____do__lift_345_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_h__1_346_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_apply_1(v_h__2_347_, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__2_347_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__1_346_, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_352_, lean_object* v_____do__lift_353_, lean_object* v_h__1_354_, lean_object* v_h__2_355_){
_start:
{
uint8_t v_____do__lift_37__boxed_356_; lean_object* v_res_357_; 
v_____do__lift_37__boxed_356_ = lean_unbox(v_____do__lift_353_);
v_res_357_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(v_motive_352_, v_____do__lift_37__boxed_356_, v_h__1_354_, v_h__2_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_){
_start:
{
if (lean_obj_tag(v_____do__lift_358_) == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_h__2_360_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_apply_1(v_h__1_359_, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_359_);
v_val_363_ = lean_ctor_get(v_____do__lift_358_, 0);
lean_inc(v_val_363_);
lean_dec_ref(v_____do__lift_358_);
v___x_364_ = lean_apply_1(v_h__2_360_, v_val_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_365_, lean_object* v_motive_366_, lean_object* v_____do__lift_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
if (lean_obj_tag(v_____do__lift_367_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_369_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_apply_1(v_h__1_368_, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_373_; 
lean_dec(v_h__1_368_);
v_val_372_ = lean_ctor_get(v_____do__lift_367_, 0);
lean_inc(v_val_372_);
lean_dec_ref(v_____do__lift_367_);
v___x_373_ = lean_apply_1(v_h__2_369_, v_val_372_);
return v___x_373_;
}
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
