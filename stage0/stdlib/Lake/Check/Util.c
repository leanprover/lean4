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
size_t v___x_16_; size_t v___x_17_; lean_object* v___x_18_; 
lean_dec(v_toPure_7_);
v___x_16_ = ((size_t)0ULL);
v___x_17_ = lean_usize_of_nat(v___x_12_);
v___x_18_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_8_, v___f_9_, v___x_11_, v___x_16_, v___x_17_, v___x_13_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__2___boxed(lean_object* v_rhs_19_, lean_object* v___x_20_, lean_object* v_toPure_21_, lean_object* v_inst_22_, lean_object* v___f_23_, lean_object* v_____r_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_Check_runForUsedConsts___redArg___lam__2(v_rhs_19_, v___x_20_, v_toPure_21_, v_inst_22_, v___f_23_, v_____r_24_);
lean_dec(v___x_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__1(lean_object* v___x_26_, lean_object* v_toPure_27_, lean_object* v_inst_28_, lean_object* v___f_29_, lean_object* v_f_30_, lean_object* v_toBind_31_, lean_object* v_rule_32_){
_start:
{
lean_object* v_ctor_33_; lean_object* v_rhs_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_ctor_33_ = lean_ctor_get(v_rule_32_, 0);
lean_inc(v_ctor_33_);
v_rhs_34_ = lean_ctor_get(v_rule_32_, 2);
lean_inc_ref(v_rhs_34_);
lean_dec_ref(v_rule_32_);
v___f_35_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_35_, 0, v_rhs_34_);
lean_closure_set(v___f_35_, 1, v___x_26_);
lean_closure_set(v___f_35_, 2, v_toPure_27_);
lean_closure_set(v___f_35_, 3, v_inst_28_);
lean_closure_set(v___f_35_, 4, v___f_29_);
v___x_36_ = lean_apply_1(v_f_30_, v_ctor_33_);
v___x_37_ = lean_apply_4(v_toBind_31_, lean_box(0), lean_box(0), v___x_36_, v___f_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__3(lean_object* v_inst_38_, lean_object* v_all_39_, lean_object* v_f_40_, lean_object* v_____r_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_List_forM___redArg(v_inst_38_, v_all_39_, v_f_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__4(lean_object* v_info_43_, lean_object* v_inst_44_, lean_object* v_f_45_, lean_object* v_toBind_46_, lean_object* v___f_47_, lean_object* v_toPure_48_, lean_object* v_____r_49_){
_start:
{
switch(lean_obj_tag(v_info_43_))
{
case 5:
{
lean_object* v_val_50_; lean_object* v_all_51_; lean_object* v_ctors_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_toPure_48_);
lean_dec(v___f_47_);
v_val_50_ = lean_ctor_get(v_info_43_, 0);
lean_inc_ref(v_val_50_);
lean_dec_ref_known(v_info_43_, 1);
v_all_51_ = lean_ctor_get(v_val_50_, 3);
lean_inc(v_all_51_);
v_ctors_52_ = lean_ctor_get(v_val_50_, 4);
lean_inc(v_ctors_52_);
lean_dec_ref(v_val_50_);
lean_inc(v_f_45_);
lean_inc_ref(v_inst_44_);
v___f_53_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__3), 4, 3);
lean_closure_set(v___f_53_, 0, v_inst_44_);
lean_closure_set(v___f_53_, 1, v_all_51_);
lean_closure_set(v___f_53_, 2, v_f_45_);
v___x_54_ = l_List_forM___redArg(v_inst_44_, v_ctors_52_, v_f_45_);
v___x_55_ = lean_apply_4(v_toBind_46_, lean_box(0), lean_box(0), v___x_54_, v___f_53_);
return v___x_55_;
}
case 6:
{
lean_object* v_val_56_; lean_object* v_induct_57_; lean_object* v___x_58_; 
lean_dec(v_toPure_48_);
lean_dec(v___f_47_);
lean_dec(v_toBind_46_);
lean_dec_ref(v_inst_44_);
v_val_56_ = lean_ctor_get(v_info_43_, 0);
lean_inc_ref(v_val_56_);
lean_dec_ref_known(v_info_43_, 1);
v_induct_57_ = lean_ctor_get(v_val_56_, 1);
lean_inc(v_induct_57_);
lean_dec_ref(v_val_56_);
v___x_58_ = lean_apply_1(v_f_45_, v_induct_57_);
return v___x_58_;
}
case 7:
{
lean_object* v_val_59_; lean_object* v_rules_60_; lean_object* v___x_61_; 
lean_dec(v_toPure_48_);
lean_dec(v_toBind_46_);
lean_dec(v_f_45_);
v_val_59_ = lean_ctor_get(v_info_43_, 0);
lean_inc_ref(v_val_59_);
lean_dec_ref_known(v_info_43_, 1);
v_rules_60_ = lean_ctor_get(v_val_59_, 6);
lean_inc(v_rules_60_);
lean_dec_ref(v_val_59_);
v___x_61_ = l_List_forM___redArg(v_inst_44_, v_rules_60_, v___f_47_);
return v___x_61_;
}
default: 
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v___f_47_);
lean_dec(v_toBind_46_);
lean_dec(v_f_45_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_info_43_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__5(lean_object* v___f_64_, lean_object* v_____r_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_apply_1(v___f_64_, v_____r_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6(lean_object* v_info_67_, lean_object* v___x_68_, lean_object* v_toPure_69_, lean_object* v_toBind_70_, lean_object* v___f_71_, lean_object* v_inst_72_, lean_object* v___f_73_, lean_object* v___f_74_, lean_object* v_____r_75_){
_start:
{
uint8_t v___x_76_; lean_object* v___x_77_; 
v___x_76_ = 1;
v___x_77_ = l_Lean_ConstantInfo_value_x3f(v_info_67_, v___x_76_);
if (lean_obj_tag(v___x_77_) == 1)
{
lean_object* v_val_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
lean_dec(v___f_74_);
v_val_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = l_Lean_Expr_getUsedConstants(v_val_78_);
v___x_80_ = lean_array_get_size(v___x_79_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_nat_dec_lt(v___x_68_, v___x_80_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v___x_79_);
lean_dec(v___f_73_);
lean_dec_ref(v_inst_72_);
v___x_83_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_81_);
v___x_84_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_83_, v___f_71_);
return v___x_84_;
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_toPure_69_);
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_of_nat(v___x_80_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_72_, v___f_73_, v___x_79_, v___x_85_, v___x_86_, v___x_81_);
v___x_88_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_87_, v___f_71_);
return v___x_88_;
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v___x_77_);
lean_dec(v___f_73_);
lean_dec_ref(v_inst_72_);
lean_dec(v___f_71_);
lean_dec(v_toBind_70_);
lean_dec(v_toPure_69_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v___f_74_, v___x_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__6___boxed(lean_object* v_info_91_, lean_object* v___x_92_, lean_object* v_toPure_93_, lean_object* v_toBind_94_, lean_object* v___f_95_, lean_object* v_inst_96_, lean_object* v___f_97_, lean_object* v___f_98_, lean_object* v_____r_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_Check_runForUsedConsts___redArg___lam__6(v_info_91_, v___x_92_, v_toPure_93_, v_toBind_94_, v___f_95_, v_inst_96_, v___f_97_, v___f_98_, v_____r_99_);
lean_dec(v___x_92_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7(lean_object* v_info_101_, lean_object* v_f_102_, lean_object* v_toBind_103_, lean_object* v___f_104_, lean_object* v_____r_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_Lean_ConstantInfo_name(v_info_101_);
v___x_107_ = lean_apply_1(v_f_102_, v___x_106_);
v___x_108_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v___x_107_, v___f_104_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg___lam__7___boxed(lean_object* v_info_109_, lean_object* v_f_110_, lean_object* v_toBind_111_, lean_object* v___f_112_, lean_object* v_____r_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lake_Check_runForUsedConsts___redArg___lam__7(v_info_109_, v_f_110_, v_toBind_111_, v___f_112_, v_____r_113_);
lean_dec_ref(v_info_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___redArg(lean_object* v_inst_115_, lean_object* v_info_116_, lean_object* v_f_117_){
_start:
{
lean_object* v_toApplicative_118_; lean_object* v_toBind_119_; lean_object* v_toPure_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___f_125_; lean_object* v___y_127_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_toApplicative_118_ = lean_ctor_get(v_inst_115_, 0);
v_toBind_119_ = lean_ctor_get(v_inst_115_, 1);
lean_inc_n(v_toBind_119_, 2);
v_toPure_120_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_inc_n(v_toPure_120_, 2);
lean_inc_n(v_f_117_, 2);
v___f_121_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__0), 3, 1);
lean_closure_set(v___f_121_, 0, v_f_117_);
v___x_122_ = l_Lean_ConstantInfo_type(v_info_116_);
v___x_123_ = l_Lean_Expr_getUsedConstants(v___x_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___f_121_);
lean_inc_ref(v_inst_115_);
v___f_125_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__1), 7, 6);
lean_closure_set(v___f_125_, 0, v___x_124_);
lean_closure_set(v___f_125_, 1, v_toPure_120_);
lean_closure_set(v___f_125_, 2, v_inst_115_);
lean_closure_set(v___f_125_, 3, v___f_121_);
lean_closure_set(v___f_125_, 4, v_f_117_);
lean_closure_set(v___f_125_, 5, v_toBind_119_);
v___x_133_ = lean_array_get_size(v___x_123_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_nat_dec_lt(v___x_124_, v___x_133_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec_ref(v___x_123_);
lean_inc(v_toPure_120_);
v___x_136_ = lean_apply_2(v_toPure_120_, lean_box(0), v___x_134_);
v___y_127_ = v___x_136_;
goto v___jp_126_;
}
else
{
size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_133_);
lean_inc_ref(v___f_121_);
lean_inc_ref(v_inst_115_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_115_, v___f_121_, v___x_123_, v___x_137_, v___x_138_, v___x_134_);
v___y_127_ = v___x_139_;
goto v___jp_126_;
}
v___jp_126_:
{
lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
lean_inc(v_toPure_120_);
lean_inc_n(v_toBind_119_, 3);
lean_inc(v_f_117_);
lean_inc_ref(v_inst_115_);
lean_inc_ref_n(v_info_116_, 2);
v___f_128_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__4), 7, 6);
lean_closure_set(v___f_128_, 0, v_info_116_);
lean_closure_set(v___f_128_, 1, v_inst_115_);
lean_closure_set(v___f_128_, 2, v_f_117_);
lean_closure_set(v___f_128_, 3, v_toBind_119_);
lean_closure_set(v___f_128_, 4, v___f_125_);
lean_closure_set(v___f_128_, 5, v_toPure_120_);
lean_inc_ref(v___f_128_);
v___f_129_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__5), 2, 1);
lean_closure_set(v___f_129_, 0, v___f_128_);
v___f_130_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_130_, 0, v_info_116_);
lean_closure_set(v___f_130_, 1, v___x_124_);
lean_closure_set(v___f_130_, 2, v_toPure_120_);
lean_closure_set(v___f_130_, 3, v_toBind_119_);
lean_closure_set(v___f_130_, 4, v___f_129_);
lean_closure_set(v___f_130_, 5, v_inst_115_);
lean_closure_set(v___f_130_, 6, v___f_121_);
lean_closure_set(v___f_130_, 7, v___f_128_);
v___f_131_ = lean_alloc_closure((void*)(l_Lake_Check_runForUsedConsts___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_131_, 0, v_info_116_);
lean_closure_set(v___f_131_, 1, v_f_117_);
lean_closure_set(v___f_131_, 2, v_toBind_119_);
lean_closure_set(v___f_131_, 3, v___f_130_);
v___x_132_ = lean_apply_4(v_toBind_119_, lean_box(0), lean_box(0), v___y_127_, v___f_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts(lean_object* v_m_140_, lean_object* v_inst_141_, lean_object* v_info_142_, lean_object* v_f_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lake_Check_runForUsedConsts___redArg(v_inst_141_, v_info_142_, v_f_143_);
return v___x_144_;
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
