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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableExternAttrData_hash(lean_object*);
uint64_t l_Lean_Compiler_instHashableInlineAttributeKind_hash(uint8_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instHashableParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instHashableParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instHashableParam___closed__0_value;
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object* v_p_1_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object* v_p_7_){
_start:
{
uint64_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Compiler_LCNF_instHashableParam___lam__0(v_p_7_);
lean_dec_ref(v_p_7_);
v_r_9_ = lean_box_uint64(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t v_pu_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___closed__0));
return v___f_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object* v_pu_13_){
_start:
{
uint8_t v_pu_boxed_14_; lean_object* v_res_15_; 
v_pu_boxed_14_ = lean_unbox(v_pu_13_);
v_res_15_ = l_Lean_Compiler_LCNF_instHashableParam(v_pu_boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object* v_as_16_, size_t v_i_17_, size_t v_stop_18_, uint64_t v_b_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_usize_dec_eq(v_i_17_, v_stop_18_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v_fvarId_22_; lean_object* v_type_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; 
v___x_21_ = lean_array_uget_borrowed(v_as_16_, v_i_17_);
v_fvarId_22_ = lean_ctor_get(v___x_21_, 0);
v_type_23_ = lean_ctor_get(v___x_21_, 2);
v___x_24_ = l_Lean_instHashableFVarId_hash(v_fvarId_22_);
v___x_25_ = l_Lean_Expr_hash(v_type_23_);
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
v___x_27_ = lean_uint64_mix_hash(v_b_19_, v___x_26_);
v___x_28_ = ((size_t)1ULL);
v___x_29_ = lean_usize_add(v_i_17_, v___x_28_);
v_i_17_ = v___x_29_;
v_b_19_ = v___x_27_;
goto _start;
}
else
{
return v_b_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* v_as_31_, lean_object* v_i_32_, lean_object* v_stop_33_, lean_object* v_b_34_){
_start:
{
size_t v_i_boxed_35_; size_t v_stop_boxed_36_; uint64_t v_b_boxed_37_; uint64_t v_res_38_; lean_object* v_r_39_; 
v_i_boxed_35_ = lean_unbox_usize(v_i_32_);
lean_dec(v_i_32_);
v_stop_boxed_36_ = lean_unbox_usize(v_stop_33_);
lean_dec(v_stop_33_);
v_b_boxed_37_ = lean_unbox_uint64(v_b_34_);
lean_dec_ref(v_b_34_);
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_as_31_, v_i_boxed_35_, v_stop_boxed_36_, v_b_boxed_37_);
lean_dec_ref(v_as_31_);
v_r_39_ = lean_box_uint64(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object* v_ps_40_){
_start:
{
uint64_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = 7ULL;
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_array_get_size(v_ps_40_);
v___x_44_ = lean_nat_dec_lt(v___x_42_, v___x_43_);
if (v___x_44_ == 0)
{
return v___x_41_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = lean_nat_dec_le(v___x_43_, v___x_43_);
if (v___x_45_ == 0)
{
if (v___x_44_ == 0)
{
return v___x_41_;
}
else
{
size_t v___x_46_; size_t v___x_47_; uint64_t v___x_48_; 
v___x_46_ = ((size_t)0ULL);
v___x_47_ = lean_usize_of_nat(v___x_43_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_40_, v___x_46_, v___x_47_, v___x_41_);
return v___x_48_;
}
}
else
{
size_t v___x_49_; size_t v___x_50_; uint64_t v___x_51_; 
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_43_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_40_, v___x_49_, v___x_50_, v___x_41_);
return v___x_51_;
}
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t v_pu_83_, lean_object* v_alts_84_){
_start:
{
uint64_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_85_ = 7ULL;
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_array_get_size(v_alts_84_);
v___x_88_ = lean_nat_dec_lt(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
return v___x_85_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_le(v___x_87_, v___x_87_);
if (v___x_89_ == 0)
{
if (v___x_88_ == 0)
{
return v___x_85_;
}
else
{
size_t v___x_90_; size_t v___x_91_; uint64_t v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_87_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_83_, v_alts_84_, v___x_90_, v___x_91_, v___x_85_);
return v___x_92_;
}
}
else
{
size_t v___x_93_; size_t v___x_94_; uint64_t v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_87_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_83_, v_alts_84_, v___x_93_, v___x_94_, v___x_85_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t v_pu_96_, lean_object* v_code_97_){
_start:
{
switch(lean_obj_tag(v_code_97_))
{
case 0:
{
lean_object* v_decl_98_; lean_object* v_k_99_; lean_object* v_fvarId_100_; lean_object* v_type_101_; lean_object* v_value_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; 
v_decl_98_ = lean_ctor_get(v_code_97_, 0);
v_k_99_ = lean_ctor_get(v_code_97_, 1);
v_fvarId_100_ = lean_ctor_get(v_decl_98_, 0);
v_type_101_ = lean_ctor_get(v_decl_98_, 2);
v_value_102_ = lean_ctor_get(v_decl_98_, 3);
v___x_103_ = l_Lean_instHashableFVarId_hash(v_fvarId_100_);
v___x_104_ = l_Lean_Expr_hash(v_type_101_);
v___x_105_ = lean_uint64_mix_hash(v___x_103_, v___x_104_);
v___x_106_ = l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_96_, v_value_102_);
v___x_107_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_99_);
v___x_108_ = lean_uint64_mix_hash(v___x_106_, v___x_107_);
v___x_109_ = lean_uint64_mix_hash(v___x_105_, v___x_108_);
return v___x_109_;
}
case 3:
{
lean_object* v_fvarId_110_; lean_object* v_args_111_; uint64_t v___x_112_; uint64_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_fvarId_110_ = lean_ctor_get(v_code_97_, 0);
v_args_111_ = lean_ctor_get(v_code_97_, 1);
v___x_112_ = l_Lean_instHashableFVarId_hash(v_fvarId_110_);
v___x_113_ = 7ULL;
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_get_size(v_args_111_);
v___x_116_ = lean_nat_dec_lt(v___x_114_, v___x_115_);
if (v___x_116_ == 0)
{
uint64_t v___x_117_; 
v___x_117_ = lean_uint64_mix_hash(v___x_112_, v___x_113_);
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_le(v___x_115_, v___x_115_);
if (v___x_118_ == 0)
{
if (v___x_116_ == 0)
{
uint64_t v___x_119_; 
v___x_119_ = lean_uint64_mix_hash(v___x_112_, v___x_113_);
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_115_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_111_, v___x_120_, v___x_121_, v___x_113_);
v___x_123_ = lean_uint64_mix_hash(v___x_112_, v___x_122_);
return v___x_123_;
}
}
else
{
size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_115_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_111_, v___x_124_, v___x_125_, v___x_113_);
v___x_127_ = lean_uint64_mix_hash(v___x_112_, v___x_126_);
return v___x_127_;
}
}
}
case 4:
{
lean_object* v_cases_128_; lean_object* v_resultType_129_; lean_object* v_discr_130_; lean_object* v_alts_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; 
v_cases_128_ = lean_ctor_get(v_code_97_, 0);
v_resultType_129_ = lean_ctor_get(v_cases_128_, 1);
v_discr_130_ = lean_ctor_get(v_cases_128_, 2);
v_alts_131_ = lean_ctor_get(v_cases_128_, 3);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_discr_130_);
v___x_133_ = l_Lean_Expr_hash(v_resultType_129_);
v___x_134_ = lean_uint64_mix_hash(v___x_132_, v___x_133_);
v___x_135_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_96_, v_alts_131_);
v___x_136_ = lean_uint64_mix_hash(v___x_134_, v___x_135_);
return v___x_136_;
}
case 5:
{
lean_object* v_fvarId_137_; uint64_t v___x_138_; 
v_fvarId_137_ = lean_ctor_get(v_code_97_, 0);
v___x_138_ = l_Lean_instHashableFVarId_hash(v_fvarId_137_);
return v___x_138_;
}
case 6:
{
lean_object* v_type_139_; uint64_t v___x_140_; 
v_type_139_ = lean_ctor_get(v_code_97_, 0);
v___x_140_ = l_Lean_Expr_hash(v_type_139_);
return v___x_140_;
}
case 7:
{
lean_object* v_fvarId_141_; lean_object* v_i_142_; lean_object* v_y_143_; lean_object* v_k_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; 
v_fvarId_141_ = lean_ctor_get(v_code_97_, 0);
v_i_142_ = lean_ctor_get(v_code_97_, 1);
v_y_143_ = lean_ctor_get(v_code_97_, 2);
v_k_144_ = lean_ctor_get(v_code_97_, 3);
v___x_145_ = l_Lean_instHashableFVarId_hash(v_fvarId_141_);
v___x_146_ = lean_uint64_of_nat(v_i_142_);
v___x_147_ = lean_uint64_mix_hash(v___x_145_, v___x_146_);
v___x_148_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_143_);
v___x_149_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_144_);
v___x_150_ = lean_uint64_mix_hash(v___x_148_, v___x_149_);
v___x_151_ = lean_uint64_mix_hash(v___x_147_, v___x_150_);
return v___x_151_;
}
case 8:
{
lean_object* v_fvarId_152_; lean_object* v_i_153_; lean_object* v_y_154_; lean_object* v_k_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; 
v_fvarId_152_ = lean_ctor_get(v_code_97_, 0);
v_i_153_ = lean_ctor_get(v_code_97_, 1);
v_y_154_ = lean_ctor_get(v_code_97_, 2);
v_k_155_ = lean_ctor_get(v_code_97_, 3);
v___x_156_ = l_Lean_instHashableFVarId_hash(v_fvarId_152_);
v___x_157_ = lean_uint64_of_nat(v_i_153_);
v___x_158_ = lean_uint64_mix_hash(v___x_156_, v___x_157_);
v___x_159_ = l_Lean_instHashableFVarId_hash(v_y_154_);
v___x_160_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_155_);
v___x_161_ = lean_uint64_mix_hash(v___x_159_, v___x_160_);
v___x_162_ = lean_uint64_mix_hash(v___x_158_, v___x_161_);
return v___x_162_;
}
case 9:
{
lean_object* v_fvarId_163_; lean_object* v_i_164_; lean_object* v_offset_165_; lean_object* v_y_166_; lean_object* v_ty_167_; lean_object* v_k_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; 
v_fvarId_163_ = lean_ctor_get(v_code_97_, 0);
v_i_164_ = lean_ctor_get(v_code_97_, 1);
v_offset_165_ = lean_ctor_get(v_code_97_, 2);
v_y_166_ = lean_ctor_get(v_code_97_, 3);
v_ty_167_ = lean_ctor_get(v_code_97_, 4);
v_k_168_ = lean_ctor_get(v_code_97_, 5);
v___x_169_ = l_Lean_instHashableFVarId_hash(v_fvarId_163_);
v___x_170_ = lean_uint64_of_nat(v_i_164_);
v___x_171_ = lean_uint64_mix_hash(v___x_169_, v___x_170_);
v___x_172_ = lean_uint64_of_nat(v_offset_165_);
v___x_173_ = l_Lean_instHashableFVarId_hash(v_y_166_);
v___x_174_ = lean_uint64_mix_hash(v___x_172_, v___x_173_);
v___x_175_ = l_Lean_Expr_hash(v_ty_167_);
v___x_176_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_168_);
v___x_177_ = lean_uint64_mix_hash(v___x_175_, v___x_176_);
v___x_178_ = lean_uint64_mix_hash(v___x_174_, v___x_177_);
v___x_179_ = lean_uint64_mix_hash(v___x_171_, v___x_178_);
return v___x_179_;
}
case 10:
{
lean_object* v_fvarId_180_; lean_object* v_cidx_181_; lean_object* v_k_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; 
v_fvarId_180_ = lean_ctor_get(v_code_97_, 0);
v_cidx_181_ = lean_ctor_get(v_code_97_, 1);
v_k_182_ = lean_ctor_get(v_code_97_, 2);
v___x_183_ = l_Lean_instHashableFVarId_hash(v_fvarId_180_);
v___x_184_ = lean_uint64_of_nat(v_cidx_181_);
v___x_185_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_182_);
v___x_186_ = lean_uint64_mix_hash(v___x_184_, v___x_185_);
v___x_187_ = lean_uint64_mix_hash(v___x_183_, v___x_186_);
return v___x_187_;
}
case 11:
{
lean_object* v_fvarId_188_; lean_object* v_n_189_; uint8_t v_check_190_; uint8_t v_persistent_191_; lean_object* v_k_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___y_197_; uint64_t v___y_198_; uint64_t v___y_204_; 
v_fvarId_188_ = lean_ctor_get(v_code_97_, 0);
v_n_189_ = lean_ctor_get(v_code_97_, 1);
v_check_190_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3);
v_persistent_191_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3 + 1);
v_k_192_ = lean_ctor_get(v_code_97_, 2);
v___x_193_ = l_Lean_instHashableFVarId_hash(v_fvarId_188_);
v___x_194_ = lean_uint64_of_nat(v_n_189_);
v___x_195_ = lean_uint64_mix_hash(v___x_193_, v___x_194_);
if (v_persistent_191_ == 0)
{
uint64_t v___x_207_; 
v___x_207_ = 13ULL;
v___y_204_ = v___x_207_;
goto v___jp_203_;
}
else
{
uint64_t v___x_208_; 
v___x_208_ = 11ULL;
v___y_204_ = v___x_208_;
goto v___jp_203_;
}
v___jp_196_:
{
uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; 
v___x_199_ = lean_uint64_mix_hash(v___y_197_, v___y_198_);
v___x_200_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_192_);
v___x_201_ = lean_uint64_mix_hash(v___x_199_, v___x_200_);
v___x_202_ = lean_uint64_mix_hash(v___x_195_, v___x_201_);
return v___x_202_;
}
v___jp_203_:
{
if (v_check_190_ == 0)
{
uint64_t v___x_205_; 
v___x_205_ = 13ULL;
v___y_197_ = v___y_204_;
v___y_198_ = v___x_205_;
goto v___jp_196_;
}
else
{
uint64_t v___x_206_; 
v___x_206_ = 11ULL;
v___y_197_ = v___y_204_;
v___y_198_ = v___x_206_;
goto v___jp_196_;
}
}
}
case 12:
{
lean_object* v_fvarId_209_; lean_object* v_n_210_; uint8_t v_check_211_; uint8_t v_persistent_212_; lean_object* v_objs_x3f_213_; lean_object* v_k_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___y_219_; uint64_t v___y_220_; uint64_t v___y_226_; uint64_t v___y_227_; uint64_t v___y_235_; 
v_fvarId_209_ = lean_ctor_get(v_code_97_, 0);
v_n_210_ = lean_ctor_get(v_code_97_, 1);
v_check_211_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*4);
v_persistent_212_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*4 + 1);
v_objs_x3f_213_ = lean_ctor_get(v_code_97_, 2);
v_k_214_ = lean_ctor_get(v_code_97_, 3);
v___x_215_ = l_Lean_instHashableFVarId_hash(v_fvarId_209_);
v___x_216_ = lean_uint64_of_nat(v_n_210_);
v___x_217_ = lean_uint64_mix_hash(v___x_215_, v___x_216_);
if (v_persistent_212_ == 0)
{
uint64_t v___x_238_; 
v___x_238_ = 13ULL;
v___y_235_ = v___x_238_;
goto v___jp_234_;
}
else
{
uint64_t v___x_239_; 
v___x_239_ = 11ULL;
v___y_235_ = v___x_239_;
goto v___jp_234_;
}
v___jp_218_:
{
uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; 
v___x_221_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_214_);
v___x_222_ = lean_uint64_mix_hash(v___y_220_, v___x_221_);
v___x_223_ = lean_uint64_mix_hash(v___y_219_, v___x_222_);
v___x_224_ = lean_uint64_mix_hash(v___x_217_, v___x_223_);
return v___x_224_;
}
v___jp_225_:
{
uint64_t v___x_228_; 
v___x_228_ = lean_uint64_mix_hash(v___y_226_, v___y_227_);
if (lean_obj_tag(v_objs_x3f_213_) == 0)
{
uint64_t v___x_229_; 
v___x_229_ = 11ULL;
v___y_219_ = v___x_228_;
v___y_220_ = v___x_229_;
goto v___jp_218_;
}
else
{
lean_object* v_val_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; 
v_val_230_ = lean_ctor_get(v_objs_x3f_213_, 0);
v___x_231_ = lean_uint64_of_nat(v_val_230_);
v___x_232_ = 13ULL;
v___x_233_ = lean_uint64_mix_hash(v___x_231_, v___x_232_);
v___y_219_ = v___x_228_;
v___y_220_ = v___x_233_;
goto v___jp_218_;
}
}
v___jp_234_:
{
if (v_check_211_ == 0)
{
uint64_t v___x_236_; 
v___x_236_ = 13ULL;
v___y_226_ = v___y_235_;
v___y_227_ = v___x_236_;
goto v___jp_225_;
}
else
{
uint64_t v___x_237_; 
v___x_237_ = 11ULL;
v___y_226_ = v___y_235_;
v___y_227_ = v___x_237_;
goto v___jp_225_;
}
}
}
case 13:
{
lean_object* v_fvarId_240_; lean_object* v_k_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; 
v_fvarId_240_ = lean_ctor_get(v_code_97_, 0);
v_k_241_ = lean_ctor_get(v_code_97_, 1);
v___x_242_ = l_Lean_instHashableFVarId_hash(v_fvarId_240_);
v___x_243_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_241_);
v___x_244_ = lean_uint64_mix_hash(v___x_242_, v___x_243_);
return v___x_244_;
}
default: 
{
lean_object* v_decl_245_; lean_object* v_k_246_; lean_object* v_fvarId_247_; lean_object* v_params_248_; lean_object* v_type_249_; lean_object* v_value_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_decl_245_ = lean_ctor_get(v_code_97_, 0);
v_k_246_ = lean_ctor_get(v_code_97_, 1);
v_fvarId_247_ = lean_ctor_get(v_decl_245_, 0);
v_params_248_ = lean_ctor_get(v_decl_245_, 2);
v_type_249_ = lean_ctor_get(v_decl_245_, 3);
v_value_250_ = lean_ctor_get(v_decl_245_, 4);
v___x_251_ = l_Lean_instHashableFVarId_hash(v_fvarId_247_);
v___x_252_ = l_Lean_Expr_hash(v_type_249_);
v___x_253_ = lean_uint64_mix_hash(v___x_251_, v___x_252_);
v___x_254_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_value_250_);
v___x_255_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_246_);
v___x_256_ = lean_uint64_mix_hash(v___x_254_, v___x_255_);
v___x_257_ = lean_uint64_mix_hash(v___x_253_, v___x_256_);
v___x_258_ = 7ULL;
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_array_get_size(v_params_248_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
uint64_t v___x_262_; 
v___x_262_ = lean_uint64_mix_hash(v___x_257_, v___x_258_);
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_le(v___x_260_, v___x_260_);
if (v___x_263_ == 0)
{
if (v___x_261_ == 0)
{
uint64_t v___x_264_; 
v___x_264_ = lean_uint64_mix_hash(v___x_257_, v___x_258_);
return v___x_264_;
}
else
{
size_t v___x_265_; size_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_260_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_248_, v___x_265_, v___x_266_, v___x_258_);
v___x_268_ = lean_uint64_mix_hash(v___x_257_, v___x_267_);
return v___x_268_;
}
}
else
{
size_t v___x_269_; size_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_260_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_248_, v___x_269_, v___x_270_, v___x_258_);
v___x_272_ = lean_uint64_mix_hash(v___x_257_, v___x_271_);
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_273_, lean_object* v_alt_274_){
_start:
{
switch(lean_obj_tag(v_alt_274_))
{
case 0:
{
lean_object* v_ctorName_275_; lean_object* v_params_276_; lean_object* v_code_277_; uint64_t v___y_279_; uint64_t v___y_280_; uint64_t v___y_285_; 
v_ctorName_275_ = lean_ctor_get(v_alt_274_, 0);
v_params_276_ = lean_ctor_get(v_alt_274_, 1);
v_code_277_ = lean_ctor_get(v_alt_274_, 2);
if (lean_obj_tag(v_ctorName_275_) == 0)
{
uint64_t v___x_297_; 
v___x_297_ = 1723ULL;
v___y_285_ = v___x_297_;
goto v___jp_284_;
}
else
{
uint64_t v_hash_298_; 
v_hash_298_ = lean_ctor_get_uint64(v_ctorName_275_, sizeof(void*)*2);
v___y_285_ = v_hash_298_;
goto v___jp_284_;
}
v___jp_278_:
{
uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; 
v___x_281_ = lean_uint64_mix_hash(v___y_279_, v___y_280_);
v___x_282_ = l_Lean_Compiler_LCNF_hashCode(v_pu_273_, v_code_277_);
v___x_283_ = lean_uint64_mix_hash(v___x_281_, v___x_282_);
return v___x_283_;
}
v___jp_284_:
{
uint64_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = 7ULL;
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_array_get_size(v_params_276_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
v___y_279_ = v___y_285_;
v___y_280_ = v___x_286_;
goto v___jp_278_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_le(v___x_288_, v___x_288_);
if (v___x_290_ == 0)
{
if (v___x_289_ == 0)
{
v___y_279_ = v___y_285_;
v___y_280_ = v___x_286_;
goto v___jp_278_;
}
else
{
size_t v___x_291_; size_t v___x_292_; uint64_t v___x_293_; 
v___x_291_ = ((size_t)0ULL);
v___x_292_ = lean_usize_of_nat(v___x_288_);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_276_, v___x_291_, v___x_292_, v___x_286_);
v___y_279_ = v___y_285_;
v___y_280_ = v___x_293_;
goto v___jp_278_;
}
}
else
{
size_t v___x_294_; size_t v___x_295_; uint64_t v___x_296_; 
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_288_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_276_, v___x_294_, v___x_295_, v___x_286_);
v___y_279_ = v___y_285_;
v___y_280_ = v___x_296_;
goto v___jp_278_;
}
}
}
}
case 1:
{
lean_object* v_info_299_; lean_object* v_code_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; 
v_info_299_ = lean_ctor_get(v_alt_274_, 0);
v_code_300_ = lean_ctor_get(v_alt_274_, 1);
v___x_301_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_299_);
v___x_302_ = l_Lean_Compiler_LCNF_hashCode(v_pu_273_, v_code_300_);
v___x_303_ = lean_uint64_mix_hash(v___x_301_, v___x_302_);
return v___x_303_;
}
default: 
{
lean_object* v_code_304_; uint64_t v___x_305_; 
v_code_304_ = lean_ctor_get(v_alt_274_, 0);
v___x_305_ = l_Lean_Compiler_LCNF_hashCode(v_pu_273_, v_code_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_306_, lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_, uint64_t v_b_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_308_, v_stop_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; 
v___x_312_ = lean_array_uget_borrowed(v_as_307_, v_i_308_);
v___x_313_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_306_, v___x_312_);
v___x_314_ = lean_uint64_mix_hash(v_b_310_, v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_308_, v___x_315_);
v_i_308_ = v___x_316_;
v_b_310_ = v___x_314_;
goto _start;
}
else
{
return v_b_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_318_, lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_, lean_object* v_b_322_){
_start:
{
uint8_t v_pu_boxed_323_; size_t v_i_boxed_324_; size_t v_stop_boxed_325_; uint64_t v_b_boxed_326_; uint64_t v_res_327_; lean_object* v_r_328_; 
v_pu_boxed_323_ = lean_unbox(v_pu_318_);
v_i_boxed_324_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_325_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_b_boxed_326_ = lean_unbox_uint64(v_b_322_);
lean_dec_ref(v_b_322_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_323_, v_as_319_, v_i_boxed_324_, v_stop_boxed_325_, v_b_boxed_326_);
lean_dec_ref(v_as_319_);
v_r_328_ = lean_box_uint64(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_329_, lean_object* v_alts_330_){
_start:
{
uint8_t v_pu_boxed_331_; uint64_t v_res_332_; lean_object* v_r_333_; 
v_pu_boxed_331_ = lean_unbox(v_pu_329_);
v_res_332_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_331_, v_alts_330_);
lean_dec_ref(v_alts_330_);
v_r_333_ = lean_box_uint64(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_334_, lean_object* v_alt_335_){
_start:
{
uint8_t v_pu_boxed_336_; uint64_t v_res_337_; lean_object* v_r_338_; 
v_pu_boxed_336_ = lean_unbox(v_pu_334_);
v_res_337_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_336_, v_alt_335_);
lean_dec_ref(v_alt_335_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_339_, lean_object* v_code_340_){
_start:
{
uint8_t v_pu_boxed_341_; uint64_t v_res_342_; lean_object* v_r_343_; 
v_pu_boxed_341_ = lean_unbox(v_pu_339_);
v_res_342_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_341_, v_code_340_);
lean_dec_ref(v_code_340_);
v_r_343_ = lean_box_uint64(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_344_, lean_object* v_as_345_, size_t v_i_346_, size_t v_stop_347_, uint64_t v_b_348_){
_start:
{
uint64_t v___x_349_; 
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_345_, v_i_346_, v_stop_347_, v_b_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_350_, lean_object* v_as_351_, lean_object* v_i_352_, lean_object* v_stop_353_, lean_object* v_b_354_){
_start:
{
uint8_t v_pu_boxed_355_; size_t v_i_boxed_356_; size_t v_stop_boxed_357_; uint64_t v_b_boxed_358_; uint64_t v_res_359_; lean_object* v_r_360_; 
v_pu_boxed_355_ = lean_unbox(v_pu_350_);
v_i_boxed_356_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_stop_boxed_357_ = lean_unbox_usize(v_stop_353_);
lean_dec(v_stop_353_);
v_b_boxed_358_ = lean_unbox_uint64(v_b_354_);
lean_dec_ref(v_b_354_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_355_, v_as_351_, v_i_boxed_356_, v_stop_boxed_357_, v_b_boxed_358_);
lean_dec_ref(v_as_351_);
v_r_360_ = lean_box_uint64(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_361_, lean_object* v_c_362_){
_start:
{
uint64_t v___x_363_; 
v___x_363_ = l_Lean_Compiler_LCNF_hashCode(v_pu_361_, v_c_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_364_, lean_object* v_c_365_){
_start:
{
uint8_t v_pu_boxed_366_; uint64_t v_res_367_; lean_object* v_r_368_; 
v_pu_boxed_366_ = lean_unbox(v_pu_364_);
v_res_367_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_366_, v_c_365_);
lean_dec_ref(v_c_365_);
v_r_368_ = lean_box_uint64(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___f_371_; 
v___x_370_ = lean_box(v_pu_369_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_371_, 0, v___x_370_);
return v___f_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_372_){
_start:
{
uint8_t v_pu_boxed_373_; lean_object* v_res_374_; 
v_pu_boxed_373_ = lean_unbox(v_pu_372_);
v_res_374_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_373_);
return v_res_374_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v_code_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; 
v_code_377_ = lean_ctor_get(v_x_376_, 0);
v___x_378_ = 0ULL;
v___x_379_ = l_Lean_Compiler_LCNF_hashCode(v_pu_375_, v_code_377_);
v___x_380_ = lean_uint64_mix_hash(v___x_378_, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v_externAttrData_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; 
v_externAttrData_381_ = lean_ctor_get(v_x_376_, 0);
v___x_382_ = 1ULL;
v___x_383_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_381_);
v___x_384_ = lean_uint64_mix_hash(v___x_382_, v___x_383_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_pu_47__boxed_387_; uint64_t v_res_388_; lean_object* v_r_389_; 
v_pu_47__boxed_387_ = lean_unbox(v_pu_385_);
v_res_388_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_387_, v_x_386_);
lean_dec_ref(v_x_386_);
v_r_389_ = lean_box_uint64(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_box(v_pu_390_);
v___x_392_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* v_pu_393_){
_start:
{
uint8_t v_pu_5__boxed_394_; lean_object* v_res_395_; 
v_pu_5__boxed_394_ = lean_unbox(v_pu_393_);
v_res_395_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_394_);
return v_res_395_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_396_, lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
return v_x_396_;
}
else
{
lean_object* v_head_398_; lean_object* v_tail_399_; uint64_t v___y_401_; 
v_head_398_ = lean_ctor_get(v_x_397_, 0);
v_tail_399_ = lean_ctor_get(v_x_397_, 1);
if (lean_obj_tag(v_head_398_) == 0)
{
uint64_t v___x_404_; 
v___x_404_ = 1723ULL;
v___y_401_ = v___x_404_;
goto v___jp_400_;
}
else
{
uint64_t v_hash_405_; 
v_hash_405_ = lean_ctor_get_uint64(v_head_398_, sizeof(void*)*2);
v___y_401_ = v_hash_405_;
goto v___jp_400_;
}
v___jp_400_:
{
uint64_t v___x_402_; 
v___x_402_ = lean_uint64_mix_hash(v_x_396_, v___y_401_);
v_x_396_ = v___x_402_;
v_x_397_ = v_tail_399_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
uint64_t v_x_201__boxed_408_; uint64_t v_res_409_; lean_object* v_r_410_; 
v_x_201__boxed_408_ = lean_unbox_uint64(v_x_406_);
lean_dec_ref(v_x_406_);
v_res_409_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_201__boxed_408_, v_x_407_);
lean_dec(v_x_407_);
v_r_410_ = lean_box_uint64(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_411_){
_start:
{
lean_object* v_name_412_; lean_object* v_levelParams_413_; lean_object* v_type_414_; lean_object* v_params_415_; uint8_t v_safe_416_; uint64_t v___y_418_; uint64_t v___y_419_; uint64_t v___x_425_; uint64_t v___y_427_; 
v_name_412_ = lean_ctor_get(v_x_411_, 0);
v_levelParams_413_ = lean_ctor_get(v_x_411_, 1);
v_type_414_ = lean_ctor_get(v_x_411_, 2);
v_params_415_ = lean_ctor_get(v_x_411_, 3);
v_safe_416_ = lean_ctor_get_uint8(v_x_411_, sizeof(void*)*4);
v___x_425_ = 0ULL;
if (lean_obj_tag(v_name_412_) == 0)
{
uint64_t v___x_444_; 
v___x_444_ = 1723ULL;
v___y_427_ = v___x_444_;
goto v___jp_426_;
}
else
{
uint64_t v_hash_445_; 
v_hash_445_ = lean_ctor_get_uint64(v_name_412_, sizeof(void*)*2);
v___y_427_ = v_hash_445_;
goto v___jp_426_;
}
v___jp_417_:
{
uint64_t v___x_420_; 
v___x_420_ = lean_uint64_mix_hash(v___y_418_, v___y_419_);
if (v_safe_416_ == 0)
{
uint64_t v___x_421_; uint64_t v___x_422_; 
v___x_421_ = 13ULL;
v___x_422_ = lean_uint64_mix_hash(v___x_420_, v___x_421_);
return v___x_422_;
}
else
{
uint64_t v___x_423_; uint64_t v___x_424_; 
v___x_423_ = 11ULL;
v___x_424_ = lean_uint64_mix_hash(v___x_420_, v___x_423_);
return v___x_424_;
}
}
v___jp_426_:
{
uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_428_ = lean_uint64_mix_hash(v___x_425_, v___y_427_);
v___x_429_ = 7ULL;
v___x_430_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_429_, v_levelParams_413_);
v___x_431_ = lean_uint64_mix_hash(v___x_428_, v___x_430_);
v___x_432_ = l_Lean_Expr_hash(v_type_414_);
v___x_433_ = lean_uint64_mix_hash(v___x_431_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_array_get_size(v_params_415_);
v___x_436_ = lean_nat_dec_lt(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
v___y_418_ = v___x_433_;
v___y_419_ = v___x_429_;
goto v___jp_417_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v___x_435_, v___x_435_);
if (v___x_437_ == 0)
{
if (v___x_436_ == 0)
{
v___y_418_ = v___x_433_;
v___y_419_ = v___x_429_;
goto v___jp_417_;
}
else
{
size_t v___x_438_; size_t v___x_439_; uint64_t v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_435_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_415_, v___x_438_, v___x_439_, v___x_429_);
v___y_418_ = v___x_433_;
v___y_419_ = v___x_440_;
goto v___jp_417_;
}
}
else
{
size_t v___x_441_; size_t v___x_442_; uint64_t v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_435_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_415_, v___x_441_, v___x_442_, v___x_429_);
v___y_418_ = v___x_433_;
v___y_419_ = v___x_443_;
goto v___jp_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_446_){
_start:
{
uint64_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_446_);
lean_dec_ref(v_x_446_);
v_r_448_ = lean_box_uint64(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_449_, lean_object* v_x_450_){
_start:
{
uint64_t v___x_451_; 
v___x_451_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_pu_290__boxed_454_; uint64_t v_res_455_; lean_object* v_r_456_; 
v_pu_290__boxed_454_ = lean_unbox(v_pu_452_);
v_res_455_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_290__boxed_454_, v_x_453_);
lean_dec_ref(v_x_453_);
v_r_456_ = lean_box_uint64(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_box(v_pu_457_);
v___x_459_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* v_pu_460_){
_start:
{
uint8_t v_pu_5__boxed_461_; lean_object* v_res_462_; 
v_pu_5__boxed_461_ = lean_unbox(v_pu_460_);
v_res_462_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_461_);
return v_res_462_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_toSignature_465_; lean_object* v_value_466_; uint8_t v_recursive_467_; lean_object* v_inlineAttr_x3f_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___y_475_; 
v_toSignature_465_ = lean_ctor_get(v_x_464_, 0);
v_value_466_ = lean_ctor_get(v_x_464_, 1);
v_recursive_467_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*3);
v_inlineAttr_x3f_468_ = lean_ctor_get(v_x_464_, 2);
v___x_469_ = 0ULL;
v___x_470_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_465_);
v___x_471_ = lean_uint64_mix_hash(v___x_469_, v___x_470_);
v___x_472_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_463_, v_value_466_);
v___x_473_ = lean_uint64_mix_hash(v___x_471_, v___x_472_);
if (v_recursive_467_ == 0)
{
uint64_t v___x_485_; 
v___x_485_ = 13ULL;
v___y_475_ = v___x_485_;
goto v___jp_474_;
}
else
{
uint64_t v___x_486_; 
v___x_486_ = 11ULL;
v___y_475_ = v___x_486_;
goto v___jp_474_;
}
v___jp_474_:
{
uint64_t v___x_476_; 
v___x_476_ = lean_uint64_mix_hash(v___x_473_, v___y_475_);
if (lean_obj_tag(v_inlineAttr_x3f_468_) == 0)
{
uint64_t v___x_477_; uint64_t v___x_478_; 
v___x_477_ = 11ULL;
v___x_478_ = lean_uint64_mix_hash(v___x_476_, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v_val_479_; uint8_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; 
v_val_479_ = lean_ctor_get(v_inlineAttr_x3f_468_, 0);
v___x_480_ = lean_unbox(v_val_479_);
v___x_481_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_480_);
v___x_482_ = 13ULL;
v___x_483_ = lean_uint64_mix_hash(v___x_481_, v___x_482_);
v___x_484_ = lean_uint64_mix_hash(v___x_476_, v___x_483_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_pu_91__boxed_489_; uint64_t v_res_490_; lean_object* v_r_491_; 
v_pu_91__boxed_489_ = lean_unbox(v_pu_487_);
v_res_490_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_91__boxed_489_, v_x_488_);
lean_dec_ref(v_x_488_);
v_r_491_ = lean_box_uint64(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(v_pu_492_);
v___x_494_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* v_pu_495_){
_start:
{
uint8_t v_pu_5__boxed_496_; lean_object* v_res_497_; 
v_pu_5__boxed_496_ = lean_unbox(v_pu_495_);
v_res_497_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_496_);
return v_res_497_;
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
