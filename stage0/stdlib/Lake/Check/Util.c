// Lean compiler output
// Module: Lake.Check.Util
// Imports: public import Lean.Declaration public import Lean.Util.FoldConsts
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
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__0(lean_object* v_f_1_, lean_object* v_x_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_1(v_f_1_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__2(lean_object* v_rhs_5_, lean_object* v___x_6_, lean_object* v_toPure_7_, lean_object* v_inst_8_, lean_object* v___f_9_, lean_object* v_____r_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_11_ = l_Lean_Expr_getUsedConstants(v_rhs_5_);
v___x_12_ = lean_array_get_size(v___x_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_nat_dec_lt(v___x_6_, v___x_12_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref(v___x_11_);
lean_dec(v___f_9_);
lean_dec_ref(v_inst_8_);
v___x_15_ = lean_apply_2(v_toPure_7_, lean_box(0), v___x_13_);
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_le(v___x_12_, v___x_12_);
if (v___x_16_ == 0)
{
if (v___x_14_ == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_11_);
lean_dec(v___f_9_);
lean_dec_ref(v_inst_8_);
v___x_17_ = lean_apply_2(v_toPure_7_, lean_box(0), v___x_13_);
return v___x_17_;
}
else
{
size_t v___x_18_; size_t v___x_19_; lean_object* v___x_20_; 
lean_dec(v_toPure_7_);
v___x_18_ = ((size_t)0ULL);
v___x_19_ = lean_usize_of_nat(v___x_12_);
v___x_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_8_, v___f_9_, v___x_11_, v___x_18_, v___x_19_, v___x_13_);
return v___x_20_;
}
}
else
{
size_t v___x_21_; size_t v___x_22_; lean_object* v___x_23_; 
lean_dec(v_toPure_7_);
v___x_21_ = ((size_t)0ULL);
v___x_22_ = lean_usize_of_nat(v___x_12_);
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_8_, v___f_9_, v___x_11_, v___x_21_, v___x_22_, v___x_13_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__2___boxed(lean_object* v_rhs_24_, lean_object* v___x_25_, lean_object* v_toPure_26_, lean_object* v_inst_27_, lean_object* v___f_28_, lean_object* v_____r_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_Check_runForUsedConsts___redArg___lam__2(v_rhs_24_, v___x_25_, v_toPure_26_, v_inst_27_, v___f_28_, v_____r_29_);
lean_dec(v___x_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__1(lean_object* v___x_31_, lean_object* v_toPure_32_, lean_object* v_inst_33_, lean_object* v___f_34_, lean_object* v_f_35_, lean_object* v_toBind_36_, lean_object* v_rule_37_){
_start:
{
lean_object* v_ctor_38_; lean_object* v_rhs_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_ctor_38_ = lean_ctor_get(v_rule_37_, 0);
lean_inc(v_ctor_38_);
v_rhs_39_ = lean_ctor_get(v_rule_37_, 2);
lean_inc_ref(v_rhs_39_);
lean_dec_ref(v_rule_37_);
v___f_40_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_40_, 0, v_rhs_39_);
lean_closure_set(v___f_40_, 1, v___x_31_);
lean_closure_set(v___f_40_, 2, v_toPure_32_);
lean_closure_set(v___f_40_, 3, v_inst_33_);
lean_closure_set(v___f_40_, 4, v___f_34_);
v___x_41_ = lean_apply_1(v_f_35_, v_ctor_38_);
v___x_42_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_41_, v___f_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__3(lean_object* v_inst_43_, lean_object* v_all_44_, lean_object* v_f_45_, lean_object* v_____r_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_List_forM___redArg(v_inst_43_, v_all_44_, v_f_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__4(lean_object* v_info_48_, lean_object* v_inst_49_, lean_object* v_f_50_, lean_object* v_toBind_51_, lean_object* v___f_52_, lean_object* v_toPure_53_, lean_object* v_____r_54_){
_start:
{
switch(lean_obj_tag(v_info_48_))
{
case 5:
{
lean_object* v_val_55_; lean_object* v_all_56_; lean_object* v_ctors_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_toPure_53_);
lean_dec(v___f_52_);
v_val_55_ = lean_ctor_get(v_info_48_, 0);
lean_inc_ref(v_val_55_);
lean_dec_ref_known(v_info_48_, 1);
v_all_56_ = lean_ctor_get(v_val_55_, 3);
lean_inc(v_all_56_);
v_ctors_57_ = lean_ctor_get(v_val_55_, 4);
lean_inc(v_ctors_57_);
lean_dec_ref(v_val_55_);
lean_inc(v_f_50_);
lean_inc_ref(v_inst_49_);
v___f_58_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__3), 4, 3);
lean_closure_set(v___f_58_, 0, v_inst_49_);
lean_closure_set(v___f_58_, 1, v_all_56_);
lean_closure_set(v___f_58_, 2, v_f_50_);
v___x_59_ = l_List_forM___redArg(v_inst_49_, v_ctors_57_, v_f_50_);
v___x_60_ = lean_apply_4(v_toBind_51_, lean_box(0), lean_box(0), v___x_59_, v___f_58_);
return v___x_60_;
}
case 6:
{
lean_object* v_val_61_; lean_object* v_induct_62_; lean_object* v___x_63_; 
lean_dec(v_toPure_53_);
lean_dec(v___f_52_);
lean_dec(v_toBind_51_);
lean_dec_ref(v_inst_49_);
v_val_61_ = lean_ctor_get(v_info_48_, 0);
lean_inc_ref(v_val_61_);
lean_dec_ref_known(v_info_48_, 1);
v_induct_62_ = lean_ctor_get(v_val_61_, 1);
lean_inc(v_induct_62_);
lean_dec_ref(v_val_61_);
v___x_63_ = lean_apply_1(v_f_50_, v_induct_62_);
return v___x_63_;
}
case 7:
{
lean_object* v_val_64_; lean_object* v_rules_65_; lean_object* v___x_66_; 
lean_dec(v_toPure_53_);
lean_dec(v_toBind_51_);
lean_dec(v_f_50_);
v_val_64_ = lean_ctor_get(v_info_48_, 0);
lean_inc_ref(v_val_64_);
lean_dec_ref_known(v_info_48_, 1);
v_rules_65_ = lean_ctor_get(v_val_64_, 6);
lean_inc(v_rules_65_);
lean_dec_ref(v_val_64_);
v___x_66_ = l_List_forM___redArg(v_inst_49_, v_rules_65_, v___f_52_);
return v___x_66_;
}
default: 
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v___f_52_);
lean_dec(v_toBind_51_);
lean_dec(v_f_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_info_48_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_2(v_toPure_53_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__5(lean_object* v___f_69_, lean_object* v_____r_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_apply_1(v___f_69_, v_____r_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6(lean_object* v_info_72_, lean_object* v___x_73_, lean_object* v_toPure_74_, lean_object* v_toBind_75_, lean_object* v___f_76_, lean_object* v_inst_77_, lean_object* v___f_78_, lean_object* v___f_79_, lean_object* v_____r_80_){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 1;
v___x_82_ = l_Lean_ConstantInfo_value_x3f(v_info_72_, v___x_81_);
if (lean_obj_tag(v___x_82_) == 1)
{
lean_object* v_val_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
lean_dec(v___f_79_);
v_val_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = l_Lean_Expr_getUsedConstants(v_val_83_);
v___x_85_ = lean_array_get_size(v___x_84_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_nat_dec_lt(v___x_73_, v___x_85_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec_ref(v___x_84_);
lean_dec(v___f_78_);
lean_dec_ref(v_inst_77_);
v___x_88_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_86_);
v___x_89_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_88_, v___f_76_);
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_le(v___x_85_, v___x_85_);
if (v___x_90_ == 0)
{
if (v___x_87_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec_ref(v___x_84_);
lean_dec(v___f_78_);
lean_dec_ref(v_inst_77_);
v___x_91_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_86_);
v___x_92_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_91_, v___f_76_);
return v___x_92_;
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_toPure_74_);
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_85_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_77_, v___f_78_, v___x_84_, v___x_93_, v___x_94_, v___x_86_);
v___x_96_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_95_, v___f_76_);
return v___x_96_;
}
}
else
{
size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_toPure_74_);
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_85_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_77_, v___f_78_, v___x_84_, v___x_97_, v___x_98_, v___x_86_);
v___x_100_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_99_, v___f_76_);
return v___x_100_;
}
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v___x_82_);
lean_dec(v___f_78_);
lean_dec_ref(v_inst_77_);
lean_dec(v___f_76_);
lean_dec(v_toBind_75_);
lean_dec(v_toPure_74_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v___f_79_, v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6___boxed(lean_object* v_info_103_, lean_object* v___x_104_, lean_object* v_toPure_105_, lean_object* v_toBind_106_, lean_object* v___f_107_, lean_object* v_inst_108_, lean_object* v___f_109_, lean_object* v___f_110_, lean_object* v_____r_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lake_Check_runForUsedConsts___redArg___lam__6(v_info_103_, v___x_104_, v_toPure_105_, v_toBind_106_, v___f_107_, v_inst_108_, v___f_109_, v___f_110_, v_____r_111_);
lean_dec(v___x_104_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7(lean_object* v_info_113_, lean_object* v_f_114_, lean_object* v_toBind_115_, lean_object* v___f_116_, lean_object* v_____r_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = l_Lean_ConstantInfo_name(v_info_113_);
v___x_119_ = lean_apply_1(v_f_114_, v___x_118_);
v___x_120_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v___x_119_, v___f_116_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7___boxed(lean_object* v_info_121_, lean_object* v_f_122_, lean_object* v_toBind_123_, lean_object* v___f_124_, lean_object* v_____r_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_Check_runForUsedConsts___redArg___lam__7(v_info_121_, v_f_122_, v_toBind_123_, v___f_124_, v_____r_125_);
lean_dec_ref(v_info_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg(lean_object* v_inst_127_, lean_object* v_info_128_, lean_object* v_f_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toBind_131_; lean_object* v_toPure_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___y_139_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_127_, 0);
v_toBind_131_ = lean_ctor_get(v_inst_127_, 1);
lean_inc_n(v_toBind_131_, 2);
v_toPure_132_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_inc_n(v_toPure_132_, 2);
lean_inc_n(v_f_129_, 2);
v___f_133_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__0), 3, 1);
lean_closure_set(v___f_133_, 0, v_f_129_);
v___x_134_ = l_Lean_ConstantInfo_type(v_info_128_);
v___x_135_ = l_Lean_Expr_getUsedConstants(v___x_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___f_133_);
lean_inc_ref(v_inst_127_);
v___f_137_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__1), 7, 6);
lean_closure_set(v___f_137_, 0, v___x_136_);
lean_closure_set(v___f_137_, 1, v_toPure_132_);
lean_closure_set(v___f_137_, 2, v_inst_127_);
lean_closure_set(v___f_137_, 3, v___f_133_);
lean_closure_set(v___f_137_, 4, v_f_129_);
lean_closure_set(v___f_137_, 5, v_toBind_131_);
v___x_145_ = lean_array_get_size(v___x_135_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_nat_dec_lt(v___x_136_, v___x_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref(v___x_135_);
lean_inc(v_toPure_132_);
v___x_148_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_146_);
v___y_139_ = v___x_148_;
goto v___jp_138_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_le(v___x_145_, v___x_145_);
if (v___x_149_ == 0)
{
if (v___x_147_ == 0)
{
lean_object* v___x_150_; 
lean_dec_ref(v___x_135_);
lean_inc(v_toPure_132_);
v___x_150_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_146_);
v___y_139_ = v___x_150_;
goto v___jp_138_;
}
else
{
size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((size_t)0ULL);
v___x_152_ = lean_usize_of_nat(v___x_145_);
lean_inc_ref(v___f_133_);
lean_inc_ref(v_inst_127_);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_127_, v___f_133_, v___x_135_, v___x_151_, v___x_152_, v___x_146_);
v___y_139_ = v___x_153_;
goto v___jp_138_;
}
}
else
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_145_);
lean_inc_ref(v___f_133_);
lean_inc_ref(v_inst_127_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_127_, v___f_133_, v___x_135_, v___x_154_, v___x_155_, v___x_146_);
v___y_139_ = v___x_156_;
goto v___jp_138_;
}
}
v___jp_138_:
{
lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; 
lean_inc(v_toPure_132_);
lean_inc_n(v_toBind_131_, 3);
lean_inc(v_f_129_);
lean_inc_ref(v_inst_127_);
lean_inc_ref_n(v_info_128_, 2);
v___f_140_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__4), 7, 6);
lean_closure_set(v___f_140_, 0, v_info_128_);
lean_closure_set(v___f_140_, 1, v_inst_127_);
lean_closure_set(v___f_140_, 2, v_f_129_);
lean_closure_set(v___f_140_, 3, v_toBind_131_);
lean_closure_set(v___f_140_, 4, v___f_137_);
lean_closure_set(v___f_140_, 5, v_toPure_132_);
lean_inc_ref(v___f_140_);
v___f_141_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__5), 2, 1);
lean_closure_set(v___f_141_, 0, v___f_140_);
v___f_142_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_142_, 0, v_info_128_);
lean_closure_set(v___f_142_, 1, v___x_136_);
lean_closure_set(v___f_142_, 2, v_toPure_132_);
lean_closure_set(v___f_142_, 3, v_toBind_131_);
lean_closure_set(v___f_142_, 4, v___f_141_);
lean_closure_set(v___f_142_, 5, v_inst_127_);
lean_closure_set(v___f_142_, 6, v___f_133_);
lean_closure_set(v___f_142_, 7, v___f_140_);
v___f_143_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_143_, 0, v_info_128_);
lean_closure_set(v___f_143_, 1, v_f_129_);
lean_closure_set(v___f_143_, 2, v_toBind_131_);
lean_closure_set(v___f_143_, 3, v___f_142_);
v___x_144_ = lean_apply_4(v_toBind_131_, lean_box(0), lean_box(0), v___y_139_, v___f_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts(lean_object* v_m_157_, lean_object* v_inst_158_, lean_object* v_info_159_, lean_object* v_f_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lake_Check_runForUsedConsts___redArg(v_inst_158_, v_info_159_, v_f_160_);
return v___x_161_;
}
}
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_FoldConsts(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Check_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Check_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Declaration(uint8_t builtin);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Check_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Check_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Check_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Check_Util(builtin);
}
#ifdef __cplusplus
}
#endif
