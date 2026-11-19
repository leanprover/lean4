// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: public import Lean.Compiler.LCNF.Basic
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableExternAttrData_hash(lean_object*);
uint64_t l_Lean_Compiler_instHashableInlineAttributeKind_hash(uint8_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(lean_object* v_p_1_){
_start:
{
lean_object* v_fvarId_2_; lean_object* v_type_3_; uint64_t v___x_4_; uint64_t v___x_5_; uint64_t v___x_6_; 
v_fvarId_2_ = lean_ctor_get(v_p_1_, 0);
v_type_3_ = lean_ctor_get(v_p_1_, 2);
v___x_4_ = l_Lean_instHashableFVarId_hash(v_fvarId_2_);
v___x_5_ = l_Lean_Expr_hash(v_type_3_);
v___x_6_ = lean_uint64_mix_hash(v___x_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0___boxed(lean_object* v_p_7_){
_start:
{
uint64_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(v_p_7_);
lean_dec_ref(v_p_7_);
v_r_9_ = lean_box_uint64(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg(){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0));
return v___f_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Compiler_LCNF_instHashableParam___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t v_pu_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0));
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object* v_pu_17_){
_start:
{
uint8_t v_pu_boxed_18_; lean_object* v_res_19_; 
v_pu_boxed_18_ = lean_unbox(v_pu_17_);
v_res_19_ = l_Lean_Compiler_LCNF_instHashableParam(v_pu_boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object* v_as_20_, size_t v_i_21_, size_t v_stop_22_, uint64_t v_b_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = lean_usize_dec_eq(v_i_21_, v_stop_22_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v_fvarId_26_; lean_object* v_type_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; size_t v___x_32_; size_t v___x_33_; 
v___x_25_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v_fvarId_26_ = lean_ctor_get(v___x_25_, 0);
v_type_27_ = lean_ctor_get(v___x_25_, 2);
v___x_28_ = l_Lean_instHashableFVarId_hash(v_fvarId_26_);
v___x_29_ = l_Lean_Expr_hash(v_type_27_);
v___x_30_ = lean_uint64_mix_hash(v___x_28_, v___x_29_);
v___x_31_ = lean_uint64_mix_hash(v_b_23_, v___x_30_);
v___x_32_ = ((size_t)1ULL);
v___x_33_ = lean_usize_add(v_i_21_, v___x_32_);
v_i_21_ = v___x_33_;
v_b_23_ = v___x_31_;
goto _start;
}
else
{
return v_b_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* v_as_35_, lean_object* v_i_36_, lean_object* v_stop_37_, lean_object* v_b_38_){
_start:
{
size_t v_i_boxed_39_; size_t v_stop_boxed_40_; uint64_t v_b_boxed_41_; uint64_t v_res_42_; lean_object* v_r_43_; 
v_i_boxed_39_ = lean_unbox_usize(v_i_36_);
lean_dec(v_i_36_);
v_stop_boxed_40_ = lean_unbox_usize(v_stop_37_);
lean_dec(v_stop_37_);
v_b_boxed_41_ = lean_unbox_uint64(v_b_38_);
lean_dec_ref(v_b_38_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_as_35_, v_i_boxed_39_, v_stop_boxed_40_, v_b_boxed_41_);
lean_dec_ref(v_as_35_);
v_r_43_ = lean_box_uint64(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object* v_ps_44_){
_start:
{
uint64_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_45_ = 7ULL;
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_array_get_size(v_ps_44_);
v___x_48_ = lean_nat_dec_lt(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
return v___x_45_;
}
else
{
size_t v___x_49_; size_t v___x_50_; uint64_t v___x_51_; 
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_47_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_44_, v___x_49_, v___x_50_, v___x_45_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object* v_ps_52_){
_start:
{
uint64_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_52_);
lean_dec_ref(v_ps_52_);
v_r_54_ = lean_box_uint64(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t v_pu_55_, lean_object* v_ps_56_){
_start:
{
uint64_t v___x_57_; 
v___x_57_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* v_pu_58_, lean_object* v_ps_59_){
_start:
{
uint8_t v_pu_boxed_60_; uint64_t v_res_61_; lean_object* v_r_62_; 
v_pu_boxed_60_ = lean_unbox(v_pu_58_);
v_res_61_ = l_Lean_Compiler_LCNF_hashParams(v_pu_boxed_60_, v_ps_59_);
lean_dec_ref(v_ps_59_);
v_r_62_ = lean_box_uint64(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object* v_as_63_, size_t v_i_64_, size_t v_stop_65_, uint64_t v_b_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_usize_dec_eq(v_i_64_, v_stop_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; 
v___x_68_ = lean_array_uget_borrowed(v_as_63_, v_i_64_);
v___x_69_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v___x_68_);
v___x_70_ = lean_uint64_mix_hash(v_b_66_, v___x_69_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_add(v_i_64_, v___x_71_);
v_i_64_ = v___x_72_;
v_b_66_ = v___x_70_;
goto _start;
}
else
{
return v_b_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object* v_as_74_, lean_object* v_i_75_, lean_object* v_stop_76_, lean_object* v_b_77_){
_start:
{
size_t v_i_boxed_78_; size_t v_stop_boxed_79_; uint64_t v_b_boxed_80_; uint64_t v_res_81_; lean_object* v_r_82_; 
v_i_boxed_78_ = lean_unbox_usize(v_i_75_);
lean_dec(v_i_75_);
v_stop_boxed_79_ = lean_unbox_usize(v_stop_76_);
lean_dec(v_stop_76_);
v_b_boxed_80_ = lean_unbox_uint64(v_b_77_);
lean_dec_ref(v_b_77_);
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_74_, v_i_boxed_78_, v_stop_boxed_79_, v_b_boxed_80_);
lean_dec_ref(v_as_74_);
v_r_82_ = lean_box_uint64(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t v_pu_83_, lean_object* v_code_84_){
_start:
{
switch(lean_obj_tag(v_code_84_))
{
case 0:
{
lean_object* v_decl_85_; lean_object* v_k_86_; lean_object* v_fvarId_87_; lean_object* v_type_88_; lean_object* v_value_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; 
v_decl_85_ = lean_ctor_get(v_code_84_, 0);
v_k_86_ = lean_ctor_get(v_code_84_, 1);
v_fvarId_87_ = lean_ctor_get(v_decl_85_, 0);
v_type_88_ = lean_ctor_get(v_decl_85_, 2);
v_value_89_ = lean_ctor_get(v_decl_85_, 3);
v___x_90_ = l_Lean_instHashableFVarId_hash(v_fvarId_87_);
v___x_91_ = l_Lean_Expr_hash(v_type_88_);
v___x_92_ = lean_uint64_mix_hash(v___x_90_, v___x_91_);
v___x_93_ = l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_83_, v_value_89_);
v___x_94_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_86_);
v___x_95_ = lean_uint64_mix_hash(v___x_93_, v___x_94_);
v___x_96_ = lean_uint64_mix_hash(v___x_92_, v___x_95_);
return v___x_96_;
}
case 3:
{
lean_object* v_fvarId_97_; lean_object* v_args_98_; uint64_t v___x_99_; uint64_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_fvarId_97_ = lean_ctor_get(v_code_84_, 0);
v_args_98_ = lean_ctor_get(v_code_84_, 1);
v___x_99_ = l_Lean_instHashableFVarId_hash(v_fvarId_97_);
v___x_100_ = 7ULL;
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_args_98_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
uint64_t v___x_104_; 
v___x_104_ = lean_uint64_mix_hash(v___x_99_, v___x_100_);
return v___x_104_;
}
else
{
size_t v___x_105_; size_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_102_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_98_, v___x_105_, v___x_106_, v___x_100_);
v___x_108_ = lean_uint64_mix_hash(v___x_99_, v___x_107_);
return v___x_108_;
}
}
case 4:
{
lean_object* v_cases_109_; lean_object* v_resultType_110_; lean_object* v_discr_111_; lean_object* v_alts_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; 
v_cases_109_ = lean_ctor_get(v_code_84_, 0);
v_resultType_110_ = lean_ctor_get(v_cases_109_, 1);
v_discr_111_ = lean_ctor_get(v_cases_109_, 2);
v_alts_112_ = lean_ctor_get(v_cases_109_, 3);
v___x_113_ = l_Lean_instHashableFVarId_hash(v_discr_111_);
v___x_114_ = l_Lean_Expr_hash(v_resultType_110_);
v___x_115_ = lean_uint64_mix_hash(v___x_113_, v___x_114_);
v___x_116_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_83_, v_alts_112_);
v___x_117_ = lean_uint64_mix_hash(v___x_115_, v___x_116_);
return v___x_117_;
}
case 5:
{
lean_object* v_fvarId_118_; uint64_t v___x_119_; 
v_fvarId_118_ = lean_ctor_get(v_code_84_, 0);
v___x_119_ = l_Lean_instHashableFVarId_hash(v_fvarId_118_);
return v___x_119_;
}
case 6:
{
lean_object* v_type_120_; uint64_t v___x_121_; 
v_type_120_ = lean_ctor_get(v_code_84_, 0);
v___x_121_ = l_Lean_Expr_hash(v_type_120_);
return v___x_121_;
}
case 7:
{
lean_object* v_fvarId_122_; lean_object* v_i_123_; lean_object* v_y_124_; lean_object* v_k_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; 
v_fvarId_122_ = lean_ctor_get(v_code_84_, 0);
v_i_123_ = lean_ctor_get(v_code_84_, 1);
v_y_124_ = lean_ctor_get(v_code_84_, 2);
v_k_125_ = lean_ctor_get(v_code_84_, 3);
v___x_126_ = l_Lean_instHashableFVarId_hash(v_fvarId_122_);
v___x_127_ = lean_uint64_of_nat(v_i_123_);
v___x_128_ = lean_uint64_mix_hash(v___x_126_, v___x_127_);
v___x_129_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_124_);
v___x_130_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_125_);
v___x_131_ = lean_uint64_mix_hash(v___x_129_, v___x_130_);
v___x_132_ = lean_uint64_mix_hash(v___x_128_, v___x_131_);
return v___x_132_;
}
case 8:
{
lean_object* v_fvarId_133_; lean_object* v_i_134_; lean_object* v_y_135_; lean_object* v_k_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; 
v_fvarId_133_ = lean_ctor_get(v_code_84_, 0);
v_i_134_ = lean_ctor_get(v_code_84_, 1);
v_y_135_ = lean_ctor_get(v_code_84_, 2);
v_k_136_ = lean_ctor_get(v_code_84_, 3);
v___x_137_ = l_Lean_instHashableFVarId_hash(v_fvarId_133_);
v___x_138_ = lean_uint64_of_nat(v_i_134_);
v___x_139_ = lean_uint64_mix_hash(v___x_137_, v___x_138_);
v___x_140_ = l_Lean_instHashableFVarId_hash(v_y_135_);
v___x_141_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_136_);
v___x_142_ = lean_uint64_mix_hash(v___x_140_, v___x_141_);
v___x_143_ = lean_uint64_mix_hash(v___x_139_, v___x_142_);
return v___x_143_;
}
case 9:
{
lean_object* v_fvarId_144_; lean_object* v_i_145_; lean_object* v_offset_146_; lean_object* v_y_147_; lean_object* v_ty_148_; lean_object* v_k_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; 
v_fvarId_144_ = lean_ctor_get(v_code_84_, 0);
v_i_145_ = lean_ctor_get(v_code_84_, 1);
v_offset_146_ = lean_ctor_get(v_code_84_, 2);
v_y_147_ = lean_ctor_get(v_code_84_, 3);
v_ty_148_ = lean_ctor_get(v_code_84_, 4);
v_k_149_ = lean_ctor_get(v_code_84_, 5);
v___x_150_ = l_Lean_instHashableFVarId_hash(v_fvarId_144_);
v___x_151_ = lean_uint64_of_nat(v_i_145_);
v___x_152_ = lean_uint64_mix_hash(v___x_150_, v___x_151_);
v___x_153_ = lean_uint64_of_nat(v_offset_146_);
v___x_154_ = l_Lean_instHashableFVarId_hash(v_y_147_);
v___x_155_ = lean_uint64_mix_hash(v___x_153_, v___x_154_);
v___x_156_ = l_Lean_Expr_hash(v_ty_148_);
v___x_157_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_149_);
v___x_158_ = lean_uint64_mix_hash(v___x_156_, v___x_157_);
v___x_159_ = lean_uint64_mix_hash(v___x_155_, v___x_158_);
v___x_160_ = lean_uint64_mix_hash(v___x_152_, v___x_159_);
return v___x_160_;
}
case 10:
{
lean_object* v_fvarId_161_; lean_object* v_cidx_162_; lean_object* v_k_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; 
v_fvarId_161_ = lean_ctor_get(v_code_84_, 0);
v_cidx_162_ = lean_ctor_get(v_code_84_, 1);
v_k_163_ = lean_ctor_get(v_code_84_, 2);
v___x_164_ = l_Lean_instHashableFVarId_hash(v_fvarId_161_);
v___x_165_ = lean_uint64_of_nat(v_cidx_162_);
v___x_166_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_163_);
v___x_167_ = lean_uint64_mix_hash(v___x_165_, v___x_166_);
v___x_168_ = lean_uint64_mix_hash(v___x_164_, v___x_167_);
return v___x_168_;
}
case 11:
{
lean_object* v_fvarId_169_; lean_object* v_n_170_; uint8_t v_check_171_; uint8_t v_persistent_172_; lean_object* v_k_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___y_178_; uint64_t v___y_179_; uint64_t v___y_185_; 
v_fvarId_169_ = lean_ctor_get(v_code_84_, 0);
v_n_170_ = lean_ctor_get(v_code_84_, 1);
v_check_171_ = lean_ctor_get_uint8(v_code_84_, sizeof(void*)*3);
v_persistent_172_ = lean_ctor_get_uint8(v_code_84_, sizeof(void*)*3 + 1);
v_k_173_ = lean_ctor_get(v_code_84_, 2);
v___x_174_ = l_Lean_instHashableFVarId_hash(v_fvarId_169_);
v___x_175_ = lean_uint64_of_nat(v_n_170_);
v___x_176_ = lean_uint64_mix_hash(v___x_174_, v___x_175_);
if (v_persistent_172_ == 0)
{
uint64_t v___x_188_; 
v___x_188_ = 13ULL;
v___y_185_ = v___x_188_;
goto v___jp_184_;
}
else
{
uint64_t v___x_189_; 
v___x_189_ = 11ULL;
v___y_185_ = v___x_189_;
goto v___jp_184_;
}
v___jp_177_:
{
uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; 
v___x_180_ = lean_uint64_mix_hash(v___y_178_, v___y_179_);
v___x_181_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_173_);
v___x_182_ = lean_uint64_mix_hash(v___x_180_, v___x_181_);
v___x_183_ = lean_uint64_mix_hash(v___x_176_, v___x_182_);
return v___x_183_;
}
v___jp_184_:
{
if (v_check_171_ == 0)
{
uint64_t v___x_186_; 
v___x_186_ = 13ULL;
v___y_178_ = v___y_185_;
v___y_179_ = v___x_186_;
goto v___jp_177_;
}
else
{
uint64_t v___x_187_; 
v___x_187_ = 11ULL;
v___y_178_ = v___y_185_;
v___y_179_ = v___x_187_;
goto v___jp_177_;
}
}
}
case 12:
{
lean_object* v_fvarId_190_; lean_object* v_n_191_; uint8_t v_check_192_; uint8_t v_persistent_193_; lean_object* v_objs_x3f_194_; lean_object* v_k_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___y_200_; uint64_t v___y_201_; uint64_t v___y_207_; uint64_t v___y_208_; uint64_t v___y_216_; 
v_fvarId_190_ = lean_ctor_get(v_code_84_, 0);
v_n_191_ = lean_ctor_get(v_code_84_, 1);
v_check_192_ = lean_ctor_get_uint8(v_code_84_, sizeof(void*)*4);
v_persistent_193_ = lean_ctor_get_uint8(v_code_84_, sizeof(void*)*4 + 1);
v_objs_x3f_194_ = lean_ctor_get(v_code_84_, 2);
v_k_195_ = lean_ctor_get(v_code_84_, 3);
v___x_196_ = l_Lean_instHashableFVarId_hash(v_fvarId_190_);
v___x_197_ = lean_uint64_of_nat(v_n_191_);
v___x_198_ = lean_uint64_mix_hash(v___x_196_, v___x_197_);
if (v_persistent_193_ == 0)
{
uint64_t v___x_219_; 
v___x_219_ = 13ULL;
v___y_216_ = v___x_219_;
goto v___jp_215_;
}
else
{
uint64_t v___x_220_; 
v___x_220_ = 11ULL;
v___y_216_ = v___x_220_;
goto v___jp_215_;
}
v___jp_199_:
{
uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; 
v___x_202_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_195_);
v___x_203_ = lean_uint64_mix_hash(v___y_201_, v___x_202_);
v___x_204_ = lean_uint64_mix_hash(v___y_200_, v___x_203_);
v___x_205_ = lean_uint64_mix_hash(v___x_198_, v___x_204_);
return v___x_205_;
}
v___jp_206_:
{
uint64_t v___x_209_; 
v___x_209_ = lean_uint64_mix_hash(v___y_207_, v___y_208_);
if (lean_obj_tag(v_objs_x3f_194_) == 0)
{
uint64_t v___x_210_; 
v___x_210_ = 11ULL;
v___y_200_ = v___x_209_;
v___y_201_ = v___x_210_;
goto v___jp_199_;
}
else
{
lean_object* v_val_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; 
v_val_211_ = lean_ctor_get(v_objs_x3f_194_, 0);
v___x_212_ = lean_uint64_of_nat(v_val_211_);
v___x_213_ = 13ULL;
v___x_214_ = lean_uint64_mix_hash(v___x_212_, v___x_213_);
v___y_200_ = v___x_209_;
v___y_201_ = v___x_214_;
goto v___jp_199_;
}
}
v___jp_215_:
{
if (v_check_192_ == 0)
{
uint64_t v___x_217_; 
v___x_217_ = 13ULL;
v___y_207_ = v___y_216_;
v___y_208_ = v___x_217_;
goto v___jp_206_;
}
else
{
uint64_t v___x_218_; 
v___x_218_ = 11ULL;
v___y_207_ = v___y_216_;
v___y_208_ = v___x_218_;
goto v___jp_206_;
}
}
}
case 13:
{
lean_object* v_fvarId_221_; lean_object* v_k_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; 
v_fvarId_221_ = lean_ctor_get(v_code_84_, 0);
v_k_222_ = lean_ctor_get(v_code_84_, 1);
v___x_223_ = l_Lean_instHashableFVarId_hash(v_fvarId_221_);
v___x_224_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_222_);
v___x_225_ = lean_uint64_mix_hash(v___x_223_, v___x_224_);
return v___x_225_;
}
default: 
{
lean_object* v_decl_226_; lean_object* v_k_227_; lean_object* v_fvarId_228_; lean_object* v_params_229_; lean_object* v_type_230_; lean_object* v_value_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_decl_226_ = lean_ctor_get(v_code_84_, 0);
v_k_227_ = lean_ctor_get(v_code_84_, 1);
v_fvarId_228_ = lean_ctor_get(v_decl_226_, 0);
v_params_229_ = lean_ctor_get(v_decl_226_, 2);
v_type_230_ = lean_ctor_get(v_decl_226_, 3);
v_value_231_ = lean_ctor_get(v_decl_226_, 4);
v___x_232_ = l_Lean_instHashableFVarId_hash(v_fvarId_228_);
v___x_233_ = l_Lean_Expr_hash(v_type_230_);
v___x_234_ = lean_uint64_mix_hash(v___x_232_, v___x_233_);
v___x_235_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_value_231_);
v___x_236_ = l_Lean_Compiler_LCNF_hashCode(v_pu_83_, v_k_227_);
v___x_237_ = lean_uint64_mix_hash(v___x_235_, v___x_236_);
v___x_238_ = lean_uint64_mix_hash(v___x_234_, v___x_237_);
v___x_239_ = 7ULL;
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_array_get_size(v_params_229_);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
uint64_t v___x_243_; 
v___x_243_ = lean_uint64_mix_hash(v___x_238_, v___x_239_);
return v___x_243_;
}
else
{
size_t v___x_244_; size_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; 
v___x_244_ = ((size_t)0ULL);
v___x_245_ = lean_usize_of_nat(v___x_241_);
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_229_, v___x_244_, v___x_245_, v___x_239_);
v___x_247_ = lean_uint64_mix_hash(v___x_238_, v___x_246_);
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_248_, lean_object* v_alt_249_){
_start:
{
switch(lean_obj_tag(v_alt_249_))
{
case 0:
{
lean_object* v_ctorName_250_; lean_object* v_params_251_; lean_object* v_code_252_; uint64_t v___y_254_; uint64_t v___y_255_; uint64_t v___y_260_; 
v_ctorName_250_ = lean_ctor_get(v_alt_249_, 0);
v_params_251_ = lean_ctor_get(v_alt_249_, 1);
v_code_252_ = lean_ctor_get(v_alt_249_, 2);
if (lean_obj_tag(v_ctorName_250_) == 0)
{
uint64_t v___x_268_; 
v___x_268_ = 1723ULL;
v___y_260_ = v___x_268_;
goto v___jp_259_;
}
else
{
uint64_t v_hash_269_; 
v_hash_269_ = lean_ctor_get_uint64(v_ctorName_250_, sizeof(void*)*2);
v___y_260_ = v_hash_269_;
goto v___jp_259_;
}
v___jp_253_:
{
uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; 
v___x_256_ = lean_uint64_mix_hash(v___y_254_, v___y_255_);
v___x_257_ = l_Lean_Compiler_LCNF_hashCode(v_pu_248_, v_code_252_);
v___x_258_ = lean_uint64_mix_hash(v___x_256_, v___x_257_);
return v___x_258_;
}
v___jp_259_:
{
uint64_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_261_ = 7ULL;
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_size(v_params_251_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
v___y_254_ = v___y_260_;
v___y_255_ = v___x_261_;
goto v___jp_253_;
}
else
{
size_t v___x_265_; size_t v___x_266_; uint64_t v___x_267_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_263_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_251_, v___x_265_, v___x_266_, v___x_261_);
v___y_254_ = v___y_260_;
v___y_255_ = v___x_267_;
goto v___jp_253_;
}
}
}
case 1:
{
lean_object* v_info_270_; lean_object* v_code_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; 
v_info_270_ = lean_ctor_get(v_alt_249_, 0);
v_code_271_ = lean_ctor_get(v_alt_249_, 1);
v___x_272_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_270_);
v___x_273_ = l_Lean_Compiler_LCNF_hashCode(v_pu_248_, v_code_271_);
v___x_274_ = lean_uint64_mix_hash(v___x_272_, v___x_273_);
return v___x_274_;
}
default: 
{
lean_object* v_code_275_; uint64_t v___x_276_; 
v_code_275_ = lean_ctor_get(v_alt_249_, 0);
v___x_276_ = l_Lean_Compiler_LCNF_hashCode(v_pu_248_, v_code_275_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_277_, lean_object* v_as_278_, size_t v_i_279_, size_t v_stop_280_, uint64_t v_b_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_279_, v_stop_280_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; size_t v___x_286_; size_t v___x_287_; 
v___x_283_ = lean_array_uget_borrowed(v_as_278_, v_i_279_);
v___x_284_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_277_, v___x_283_);
v___x_285_ = lean_uint64_mix_hash(v_b_281_, v___x_284_);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_add(v_i_279_, v___x_286_);
v_i_279_ = v___x_287_;
v_b_281_ = v___x_285_;
goto _start;
}
else
{
return v_b_281_;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t v_pu_289_, lean_object* v_alts_290_){
_start:
{
uint64_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_291_ = 7ULL;
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_alts_290_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
return v___x_291_;
}
else
{
size_t v___x_295_; size_t v___x_296_; uint64_t v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_293_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_289_, v_alts_290_, v___x_295_, v___x_296_, v___x_291_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_298_, lean_object* v_alts_299_){
_start:
{
uint8_t v_pu_boxed_300_; uint64_t v_res_301_; lean_object* v_r_302_; 
v_pu_boxed_300_ = lean_unbox(v_pu_298_);
v_res_301_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_300_, v_alts_299_);
lean_dec_ref(v_alts_299_);
v_r_302_ = lean_box_uint64(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_303_, lean_object* v_as_304_, lean_object* v_i_305_, lean_object* v_stop_306_, lean_object* v_b_307_){
_start:
{
uint8_t v_pu_boxed_308_; size_t v_i_boxed_309_; size_t v_stop_boxed_310_; uint64_t v_b_boxed_311_; uint64_t v_res_312_; lean_object* v_r_313_; 
v_pu_boxed_308_ = lean_unbox(v_pu_303_);
v_i_boxed_309_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_stop_boxed_310_ = lean_unbox_usize(v_stop_306_);
lean_dec(v_stop_306_);
v_b_boxed_311_ = lean_unbox_uint64(v_b_307_);
lean_dec_ref(v_b_307_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_308_, v_as_304_, v_i_boxed_309_, v_stop_boxed_310_, v_b_boxed_311_);
lean_dec_ref(v_as_304_);
v_r_313_ = lean_box_uint64(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_314_, lean_object* v_alt_315_){
_start:
{
uint8_t v_pu_boxed_316_; uint64_t v_res_317_; lean_object* v_r_318_; 
v_pu_boxed_316_ = lean_unbox(v_pu_314_);
v_res_317_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_316_, v_alt_315_);
lean_dec_ref(v_alt_315_);
v_r_318_ = lean_box_uint64(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_319_, lean_object* v_code_320_){
_start:
{
uint8_t v_pu_boxed_321_; uint64_t v_res_322_; lean_object* v_r_323_; 
v_pu_boxed_321_ = lean_unbox(v_pu_319_);
v_res_322_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_321_, v_code_320_);
lean_dec_ref(v_code_320_);
v_r_323_ = lean_box_uint64(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_324_, lean_object* v_as_325_, size_t v_i_326_, size_t v_stop_327_, uint64_t v_b_328_){
_start:
{
uint64_t v___x_329_; 
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_325_, v_i_326_, v_stop_327_, v_b_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_330_, lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_stop_333_, lean_object* v_b_334_){
_start:
{
uint8_t v_pu_boxed_335_; size_t v_i_boxed_336_; size_t v_stop_boxed_337_; uint64_t v_b_boxed_338_; uint64_t v_res_339_; lean_object* v_r_340_; 
v_pu_boxed_335_ = lean_unbox(v_pu_330_);
v_i_boxed_336_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_337_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_b_boxed_338_ = lean_unbox_uint64(v_b_334_);
lean_dec_ref(v_b_334_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_335_, v_as_331_, v_i_boxed_336_, v_stop_boxed_337_, v_b_boxed_338_);
lean_dec_ref(v_as_331_);
v_r_340_ = lean_box_uint64(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_341_, lean_object* v_c_342_){
_start:
{
uint64_t v___x_343_; 
v___x_343_ = l_Lean_Compiler_LCNF_hashCode(v_pu_341_, v_c_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_344_, lean_object* v_c_345_){
_start:
{
uint8_t v_pu_boxed_346_; uint64_t v_res_347_; lean_object* v_r_348_; 
v_pu_boxed_346_ = lean_unbox(v_pu_344_);
v_res_347_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_346_, v_c_345_);
lean_dec_ref(v_c_345_);
v_r_348_ = lean_box_uint64(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___f_351_; 
v___x_350_ = lean_box(v_pu_349_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_351_, 0, v___x_350_);
return v___f_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_352_){
_start:
{
uint8_t v_pu_boxed_353_; lean_object* v_res_354_; 
v_pu_boxed_353_ = lean_unbox(v_pu_352_);
v_res_354_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_353_);
return v_res_354_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v_code_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; 
v_code_357_ = lean_ctor_get(v_x_356_, 0);
v___x_358_ = 0ULL;
v___x_359_ = l_Lean_Compiler_LCNF_hashCode(v_pu_355_, v_code_357_);
v___x_360_ = lean_uint64_mix_hash(v___x_358_, v___x_359_);
return v___x_360_;
}
else
{
lean_object* v_externAttrData_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; 
v_externAttrData_361_ = lean_ctor_get(v_x_356_, 0);
v___x_362_ = 1ULL;
v___x_363_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_361_);
v___x_364_ = lean_uint64_mix_hash(v___x_362_, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_365_, lean_object* v_x_366_){
_start:
{
uint8_t v_pu_47__boxed_367_; uint64_t v_res_368_; lean_object* v_r_369_; 
v_pu_47__boxed_367_ = lean_unbox(v_pu_365_);
v_res_368_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_367_, v_x_366_);
lean_dec_ref(v_x_366_);
v_r_369_ = lean_box_uint64(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(v_pu_370_);
v___x_372_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* v_pu_373_){
_start:
{
uint8_t v_pu_5__boxed_374_; lean_object* v_res_375_; 
v_pu_5__boxed_374_ = lean_unbox(v_pu_373_);
v_res_375_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_374_);
return v_res_375_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
return v_x_376_;
}
else
{
lean_object* v_head_378_; lean_object* v_tail_379_; uint64_t v___y_381_; 
v_head_378_ = lean_ctor_get(v_x_377_, 0);
v_tail_379_ = lean_ctor_get(v_x_377_, 1);
if (lean_obj_tag(v_head_378_) == 0)
{
uint64_t v___x_384_; 
v___x_384_ = 1723ULL;
v___y_381_ = v___x_384_;
goto v___jp_380_;
}
else
{
uint64_t v_hash_385_; 
v_hash_385_ = lean_ctor_get_uint64(v_head_378_, sizeof(void*)*2);
v___y_381_ = v_hash_385_;
goto v___jp_380_;
}
v___jp_380_:
{
uint64_t v___x_382_; 
v___x_382_ = lean_uint64_mix_hash(v_x_376_, v___y_381_);
v_x_376_ = v___x_382_;
v_x_377_ = v_tail_379_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint64_t v_x_184__boxed_388_; uint64_t v_res_389_; lean_object* v_r_390_; 
v_x_184__boxed_388_ = lean_unbox_uint64(v_x_386_);
lean_dec_ref(v_x_386_);
v_res_389_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_184__boxed_388_, v_x_387_);
lean_dec(v_x_387_);
v_r_390_ = lean_box_uint64(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_391_){
_start:
{
lean_object* v_name_392_; lean_object* v_levelParams_393_; lean_object* v_type_394_; lean_object* v_params_395_; uint8_t v_safe_396_; uint64_t v___y_398_; uint64_t v___y_399_; uint64_t v___x_405_; uint64_t v___y_407_; 
v_name_392_ = lean_ctor_get(v_x_391_, 0);
v_levelParams_393_ = lean_ctor_get(v_x_391_, 1);
v_type_394_ = lean_ctor_get(v_x_391_, 2);
v_params_395_ = lean_ctor_get(v_x_391_, 3);
v_safe_396_ = lean_ctor_get_uint8(v_x_391_, sizeof(void*)*4);
v___x_405_ = 0ULL;
if (lean_obj_tag(v_name_392_) == 0)
{
uint64_t v___x_420_; 
v___x_420_ = 1723ULL;
v___y_407_ = v___x_420_;
goto v___jp_406_;
}
else
{
uint64_t v_hash_421_; 
v_hash_421_ = lean_ctor_get_uint64(v_name_392_, sizeof(void*)*2);
v___y_407_ = v_hash_421_;
goto v___jp_406_;
}
v___jp_397_:
{
uint64_t v___x_400_; 
v___x_400_ = lean_uint64_mix_hash(v___y_398_, v___y_399_);
if (v_safe_396_ == 0)
{
uint64_t v___x_401_; uint64_t v___x_402_; 
v___x_401_ = 13ULL;
v___x_402_ = lean_uint64_mix_hash(v___x_400_, v___x_401_);
return v___x_402_;
}
else
{
uint64_t v___x_403_; uint64_t v___x_404_; 
v___x_403_ = 11ULL;
v___x_404_ = lean_uint64_mix_hash(v___x_400_, v___x_403_);
return v___x_404_;
}
}
v___jp_406_:
{
uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_408_ = lean_uint64_mix_hash(v___x_405_, v___y_407_);
v___x_409_ = 7ULL;
v___x_410_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_409_, v_levelParams_393_);
v___x_411_ = lean_uint64_mix_hash(v___x_408_, v___x_410_);
v___x_412_ = l_Lean_Expr_hash(v_type_394_);
v___x_413_ = lean_uint64_mix_hash(v___x_411_, v___x_412_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_params_395_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v___y_398_ = v___x_413_;
v___y_399_ = v___x_409_;
goto v___jp_397_;
}
else
{
size_t v___x_417_; size_t v___x_418_; uint64_t v___x_419_; 
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_415_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_395_, v___x_417_, v___x_418_, v___x_409_);
v___y_398_ = v___x_413_;
v___y_399_ = v___x_419_;
goto v___jp_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_422_){
_start:
{
uint64_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_422_);
lean_dec_ref(v_x_422_);
v_r_424_ = lean_box_uint64(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_425_, lean_object* v_x_426_){
_start:
{
uint64_t v___x_427_; 
v___x_427_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_428_, lean_object* v_x_429_){
_start:
{
uint8_t v_pu_265__boxed_430_; uint64_t v_res_431_; lean_object* v_r_432_; 
v_pu_265__boxed_430_ = lean_unbox(v_pu_428_);
v_res_431_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_265__boxed_430_, v_x_429_);
lean_dec_ref(v_x_429_);
v_r_432_ = lean_box_uint64(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(v_pu_433_);
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* v_pu_436_){
_start:
{
uint8_t v_pu_5__boxed_437_; lean_object* v_res_438_; 
v_pu_5__boxed_437_ = lean_unbox(v_pu_436_);
v_res_438_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_toSignature_441_; lean_object* v_value_442_; uint8_t v_recursive_443_; lean_object* v_inlineAttr_x3f_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___y_451_; 
v_toSignature_441_ = lean_ctor_get(v_x_440_, 0);
v_value_442_ = lean_ctor_get(v_x_440_, 1);
v_recursive_443_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*3);
v_inlineAttr_x3f_444_ = lean_ctor_get(v_x_440_, 2);
v___x_445_ = 0ULL;
v___x_446_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_441_);
v___x_447_ = lean_uint64_mix_hash(v___x_445_, v___x_446_);
v___x_448_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_439_, v_value_442_);
v___x_449_ = lean_uint64_mix_hash(v___x_447_, v___x_448_);
if (v_recursive_443_ == 0)
{
uint64_t v___x_461_; 
v___x_461_ = 13ULL;
v___y_451_ = v___x_461_;
goto v___jp_450_;
}
else
{
uint64_t v___x_462_; 
v___x_462_ = 11ULL;
v___y_451_ = v___x_462_;
goto v___jp_450_;
}
v___jp_450_:
{
uint64_t v___x_452_; 
v___x_452_ = lean_uint64_mix_hash(v___x_449_, v___y_451_);
if (lean_obj_tag(v_inlineAttr_x3f_444_) == 0)
{
uint64_t v___x_453_; uint64_t v___x_454_; 
v___x_453_ = 11ULL;
v___x_454_ = lean_uint64_mix_hash(v___x_452_, v___x_453_);
return v___x_454_;
}
else
{
lean_object* v_val_455_; uint8_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; 
v_val_455_ = lean_ctor_get(v_inlineAttr_x3f_444_, 0);
v___x_456_ = lean_unbox(v_val_455_);
v___x_457_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_456_);
v___x_458_ = 13ULL;
v___x_459_ = lean_uint64_mix_hash(v___x_457_, v___x_458_);
v___x_460_ = lean_uint64_mix_hash(v___x_452_, v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_pu_92__boxed_465_; uint64_t v_res_466_; lean_object* v_r_467_; 
v_pu_92__boxed_465_ = lean_unbox(v_pu_463_);
v_res_466_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_92__boxed_465_, v_x_464_);
lean_dec_ref(v_x_464_);
v_r_467_ = lean_box_uint64(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_box(v_pu_468_);
v___x_470_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* v_pu_471_){
_start:
{
uint8_t v_pu_5__boxed_472_; lean_object* v_res_473_; 
v_pu_5__boxed_472_ = lean_unbox(v_pu_471_);
v_res_473_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_472_);
return v_res_473_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DeclHash(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_DeclHash(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_DeclHash(builtin);
}
#ifdef __cplusplus
}
#endif
