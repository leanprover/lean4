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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_hashAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_hashAlt___closed__0;
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
lean_dec(v_b_34_);
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
lean_dec(v_b_77_);
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
static uint64_t _init_l_Lean_Compiler_LCNF_hashAlt___closed__0(void){
_start:
{
lean_object* v___x_273_; uint64_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1723u);
v___x_274_ = lean_uint64_of_nat(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_275_, lean_object* v_alt_276_){
_start:
{
switch(lean_obj_tag(v_alt_276_))
{
case 0:
{
lean_object* v_ctorName_277_; lean_object* v_params_278_; lean_object* v_code_279_; uint64_t v___y_281_; uint64_t v___y_282_; uint64_t v___y_287_; 
v_ctorName_277_ = lean_ctor_get(v_alt_276_, 0);
v_params_278_ = lean_ctor_get(v_alt_276_, 1);
v_code_279_ = lean_ctor_get(v_alt_276_, 2);
if (lean_obj_tag(v_ctorName_277_) == 0)
{
uint64_t v___x_299_; 
v___x_299_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_287_ = v___x_299_;
goto v___jp_286_;
}
else
{
uint64_t v_hash_300_; 
v_hash_300_ = lean_ctor_get_uint64(v_ctorName_277_, sizeof(void*)*2);
v___y_287_ = v_hash_300_;
goto v___jp_286_;
}
v___jp_280_:
{
uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; 
v___x_283_ = lean_uint64_mix_hash(v___y_281_, v___y_282_);
v___x_284_ = l_Lean_Compiler_LCNF_hashCode(v_pu_275_, v_code_279_);
v___x_285_ = lean_uint64_mix_hash(v___x_283_, v___x_284_);
return v___x_285_;
}
v___jp_286_:
{
uint64_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_288_ = 7ULL;
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_array_get_size(v_params_278_);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
v___y_281_ = v___y_287_;
v___y_282_ = v___x_288_;
goto v___jp_280_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_le(v___x_290_, v___x_290_);
if (v___x_292_ == 0)
{
if (v___x_291_ == 0)
{
v___y_281_ = v___y_287_;
v___y_282_ = v___x_288_;
goto v___jp_280_;
}
else
{
size_t v___x_293_; size_t v___x_294_; uint64_t v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_290_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_278_, v___x_293_, v___x_294_, v___x_288_);
v___y_281_ = v___y_287_;
v___y_282_ = v___x_295_;
goto v___jp_280_;
}
}
else
{
size_t v___x_296_; size_t v___x_297_; uint64_t v___x_298_; 
v___x_296_ = ((size_t)0ULL);
v___x_297_ = lean_usize_of_nat(v___x_290_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_278_, v___x_296_, v___x_297_, v___x_288_);
v___y_281_ = v___y_287_;
v___y_282_ = v___x_298_;
goto v___jp_280_;
}
}
}
}
case 1:
{
lean_object* v_info_301_; lean_object* v_code_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; 
v_info_301_ = lean_ctor_get(v_alt_276_, 0);
v_code_302_ = lean_ctor_get(v_alt_276_, 1);
v___x_303_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_301_);
v___x_304_ = l_Lean_Compiler_LCNF_hashCode(v_pu_275_, v_code_302_);
v___x_305_ = lean_uint64_mix_hash(v___x_303_, v___x_304_);
return v___x_305_;
}
default: 
{
lean_object* v_code_306_; uint64_t v___x_307_; 
v_code_306_ = lean_ctor_get(v_alt_276_, 0);
v___x_307_ = l_Lean_Compiler_LCNF_hashCode(v_pu_275_, v_code_306_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_308_, lean_object* v_as_309_, size_t v_i_310_, size_t v_stop_311_, uint64_t v_b_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_eq(v_i_310_, v_stop_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; 
v___x_314_ = lean_array_uget_borrowed(v_as_309_, v_i_310_);
v___x_315_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_308_, v___x_314_);
v___x_316_ = lean_uint64_mix_hash(v_b_312_, v___x_315_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_i_310_, v___x_317_);
v_i_310_ = v___x_318_;
v_b_312_ = v___x_316_;
goto _start;
}
else
{
return v_b_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_320_, lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_stop_323_, lean_object* v_b_324_){
_start:
{
uint8_t v_pu_boxed_325_; size_t v_i_boxed_326_; size_t v_stop_boxed_327_; uint64_t v_b_boxed_328_; uint64_t v_res_329_; lean_object* v_r_330_; 
v_pu_boxed_325_ = lean_unbox(v_pu_320_);
v_i_boxed_326_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_327_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_b_boxed_328_ = lean_unbox_uint64(v_b_324_);
lean_dec(v_b_324_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_325_, v_as_321_, v_i_boxed_326_, v_stop_boxed_327_, v_b_boxed_328_);
lean_dec_ref(v_as_321_);
v_r_330_ = lean_box_uint64(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_331_, lean_object* v_alts_332_){
_start:
{
uint8_t v_pu_boxed_333_; uint64_t v_res_334_; lean_object* v_r_335_; 
v_pu_boxed_333_ = lean_unbox(v_pu_331_);
v_res_334_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_333_, v_alts_332_);
lean_dec_ref(v_alts_332_);
v_r_335_ = lean_box_uint64(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_336_, lean_object* v_alt_337_){
_start:
{
uint8_t v_pu_boxed_338_; uint64_t v_res_339_; lean_object* v_r_340_; 
v_pu_boxed_338_ = lean_unbox(v_pu_336_);
v_res_339_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_338_, v_alt_337_);
lean_dec_ref(v_alt_337_);
v_r_340_ = lean_box_uint64(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_341_, lean_object* v_code_342_){
_start:
{
uint8_t v_pu_boxed_343_; uint64_t v_res_344_; lean_object* v_r_345_; 
v_pu_boxed_343_ = lean_unbox(v_pu_341_);
v_res_344_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_343_, v_code_342_);
lean_dec_ref(v_code_342_);
v_r_345_ = lean_box_uint64(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_346_, lean_object* v_as_347_, size_t v_i_348_, size_t v_stop_349_, uint64_t v_b_350_){
_start:
{
uint64_t v___x_351_; 
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_347_, v_i_348_, v_stop_349_, v_b_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_stop_355_, lean_object* v_b_356_){
_start:
{
uint8_t v_pu_boxed_357_; size_t v_i_boxed_358_; size_t v_stop_boxed_359_; uint64_t v_b_boxed_360_; uint64_t v_res_361_; lean_object* v_r_362_; 
v_pu_boxed_357_ = lean_unbox(v_pu_352_);
v_i_boxed_358_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_355_);
lean_dec(v_stop_355_);
v_b_boxed_360_ = lean_unbox_uint64(v_b_356_);
lean_dec(v_b_356_);
v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_357_, v_as_353_, v_i_boxed_358_, v_stop_boxed_359_, v_b_boxed_360_);
lean_dec_ref(v_as_353_);
v_r_362_ = lean_box_uint64(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_363_, lean_object* v_c_364_){
_start:
{
uint64_t v___x_365_; 
v___x_365_ = l_Lean_Compiler_LCNF_hashCode(v_pu_363_, v_c_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_366_, lean_object* v_c_367_){
_start:
{
uint8_t v_pu_boxed_368_; uint64_t v_res_369_; lean_object* v_r_370_; 
v_pu_boxed_368_ = lean_unbox(v_pu_366_);
v_res_369_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_368_, v_c_367_);
lean_dec_ref(v_c_367_);
v_r_370_ = lean_box_uint64(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___f_373_; 
v___x_372_ = lean_box(v_pu_371_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_373_, 0, v___x_372_);
return v___f_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_374_){
_start:
{
uint8_t v_pu_boxed_375_; lean_object* v_res_376_; 
v_pu_boxed_375_ = lean_unbox(v_pu_374_);
v_res_376_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v_code_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; 
v_code_379_ = lean_ctor_get(v_x_378_, 0);
v___x_380_ = 0ULL;
v___x_381_ = l_Lean_Compiler_LCNF_hashCode(v_pu_377_, v_code_379_);
v___x_382_ = lean_uint64_mix_hash(v___x_380_, v___x_381_);
return v___x_382_;
}
else
{
lean_object* v_externAttrData_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; 
v_externAttrData_383_ = lean_ctor_get(v_x_378_, 0);
v___x_384_ = 1ULL;
v___x_385_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_383_);
v___x_386_ = lean_uint64_mix_hash(v___x_384_, v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_387_, lean_object* v_x_388_){
_start:
{
uint8_t v_pu_47__boxed_389_; uint64_t v_res_390_; lean_object* v_r_391_; 
v_pu_47__boxed_389_ = lean_unbox(v_pu_387_);
v_res_390_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_389_, v_x_388_);
lean_dec_ref(v_x_388_);
v_r_391_ = lean_box_uint64(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(v_pu_392_);
v___x_394_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* v_pu_395_){
_start:
{
uint8_t v_pu_5__boxed_396_; lean_object* v_res_397_; 
v_pu_5__boxed_396_ = lean_unbox(v_pu_395_);
v_res_397_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_396_);
return v_res_397_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
return v_x_398_;
}
else
{
lean_object* v_head_400_; lean_object* v_tail_401_; uint64_t v___y_403_; 
v_head_400_ = lean_ctor_get(v_x_399_, 0);
v_tail_401_ = lean_ctor_get(v_x_399_, 1);
if (lean_obj_tag(v_head_400_) == 0)
{
uint64_t v___x_406_; 
v___x_406_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_403_ = v___x_406_;
goto v___jp_402_;
}
else
{
uint64_t v_hash_407_; 
v_hash_407_ = lean_ctor_get_uint64(v_head_400_, sizeof(void*)*2);
v___y_403_ = v_hash_407_;
goto v___jp_402_;
}
v___jp_402_:
{
uint64_t v___x_404_; 
v___x_404_ = lean_uint64_mix_hash(v_x_398_, v___y_403_);
v_x_398_ = v___x_404_;
v_x_399_ = v_tail_401_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
uint64_t v_x_205__boxed_410_; uint64_t v_res_411_; lean_object* v_r_412_; 
v_x_205__boxed_410_ = lean_unbox_uint64(v_x_408_);
lean_dec(v_x_408_);
v_res_411_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_205__boxed_410_, v_x_409_);
lean_dec(v_x_409_);
v_r_412_ = lean_box_uint64(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_413_){
_start:
{
lean_object* v_name_414_; lean_object* v_levelParams_415_; lean_object* v_type_416_; lean_object* v_params_417_; uint8_t v_safe_418_; uint64_t v___y_420_; uint64_t v___y_421_; uint64_t v___x_427_; uint64_t v___y_429_; 
v_name_414_ = lean_ctor_get(v_x_413_, 0);
v_levelParams_415_ = lean_ctor_get(v_x_413_, 1);
v_type_416_ = lean_ctor_get(v_x_413_, 2);
v_params_417_ = lean_ctor_get(v_x_413_, 3);
v_safe_418_ = lean_ctor_get_uint8(v_x_413_, sizeof(void*)*4);
v___x_427_ = 0ULL;
if (lean_obj_tag(v_name_414_) == 0)
{
uint64_t v___x_446_; 
v___x_446_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_429_ = v___x_446_;
goto v___jp_428_;
}
else
{
uint64_t v_hash_447_; 
v_hash_447_ = lean_ctor_get_uint64(v_name_414_, sizeof(void*)*2);
v___y_429_ = v_hash_447_;
goto v___jp_428_;
}
v___jp_419_:
{
uint64_t v___x_422_; 
v___x_422_ = lean_uint64_mix_hash(v___y_420_, v___y_421_);
if (v_safe_418_ == 0)
{
uint64_t v___x_423_; uint64_t v___x_424_; 
v___x_423_ = 13ULL;
v___x_424_ = lean_uint64_mix_hash(v___x_422_, v___x_423_);
return v___x_424_;
}
else
{
uint64_t v___x_425_; uint64_t v___x_426_; 
v___x_425_ = 11ULL;
v___x_426_ = lean_uint64_mix_hash(v___x_422_, v___x_425_);
return v___x_426_;
}
}
v___jp_428_:
{
uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_430_ = lean_uint64_mix_hash(v___x_427_, v___y_429_);
v___x_431_ = 7ULL;
v___x_432_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_431_, v_levelParams_415_);
v___x_433_ = lean_uint64_mix_hash(v___x_430_, v___x_432_);
v___x_434_ = l_Lean_Expr_hash(v_type_416_);
v___x_435_ = lean_uint64_mix_hash(v___x_433_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_array_get_size(v_params_417_);
v___x_438_ = lean_nat_dec_lt(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
v___y_420_ = v___x_435_;
v___y_421_ = v___x_431_;
goto v___jp_419_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_le(v___x_437_, v___x_437_);
if (v___x_439_ == 0)
{
if (v___x_438_ == 0)
{
v___y_420_ = v___x_435_;
v___y_421_ = v___x_431_;
goto v___jp_419_;
}
else
{
size_t v___x_440_; size_t v___x_441_; uint64_t v___x_442_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_437_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_417_, v___x_440_, v___x_441_, v___x_431_);
v___y_420_ = v___x_435_;
v___y_421_ = v___x_442_;
goto v___jp_419_;
}
}
else
{
size_t v___x_443_; size_t v___x_444_; uint64_t v___x_445_; 
v___x_443_ = ((size_t)0ULL);
v___x_444_ = lean_usize_of_nat(v___x_437_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_417_, v___x_443_, v___x_444_, v___x_431_);
v___y_420_ = v___x_435_;
v___y_421_ = v___x_445_;
goto v___jp_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_448_){
_start:
{
uint64_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_448_);
lean_dec_ref(v_x_448_);
v_r_450_ = lean_box_uint64(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_451_, lean_object* v_x_452_){
_start:
{
uint64_t v___x_453_; 
v___x_453_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_pu_298__boxed_456_; uint64_t v_res_457_; lean_object* v_r_458_; 
v_pu_298__boxed_456_ = lean_unbox(v_pu_454_);
v_res_457_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_298__boxed_456_, v_x_455_);
lean_dec_ref(v_x_455_);
v_r_458_ = lean_box_uint64(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_box(v_pu_459_);
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* v_pu_462_){
_start:
{
uint8_t v_pu_5__boxed_463_; lean_object* v_res_464_; 
v_pu_5__boxed_463_ = lean_unbox(v_pu_462_);
v_res_464_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_463_);
return v_res_464_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_toSignature_467_; lean_object* v_value_468_; uint8_t v_recursive_469_; lean_object* v_inlineAttr_x3f_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___y_477_; 
v_toSignature_467_ = lean_ctor_get(v_x_466_, 0);
v_value_468_ = lean_ctor_get(v_x_466_, 1);
v_recursive_469_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*3);
v_inlineAttr_x3f_470_ = lean_ctor_get(v_x_466_, 2);
v___x_471_ = 0ULL;
v___x_472_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_467_);
v___x_473_ = lean_uint64_mix_hash(v___x_471_, v___x_472_);
v___x_474_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_465_, v_value_468_);
v___x_475_ = lean_uint64_mix_hash(v___x_473_, v___x_474_);
if (v_recursive_469_ == 0)
{
uint64_t v___x_487_; 
v___x_487_ = 13ULL;
v___y_477_ = v___x_487_;
goto v___jp_476_;
}
else
{
uint64_t v___x_488_; 
v___x_488_ = 11ULL;
v___y_477_ = v___x_488_;
goto v___jp_476_;
}
v___jp_476_:
{
uint64_t v___x_478_; 
v___x_478_ = lean_uint64_mix_hash(v___x_475_, v___y_477_);
if (lean_obj_tag(v_inlineAttr_x3f_470_) == 0)
{
uint64_t v___x_479_; uint64_t v___x_480_; 
v___x_479_ = 11ULL;
v___x_480_ = lean_uint64_mix_hash(v___x_478_, v___x_479_);
return v___x_480_;
}
else
{
lean_object* v_val_481_; uint8_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; 
v_val_481_ = lean_ctor_get(v_inlineAttr_x3f_470_, 0);
v___x_482_ = lean_unbox(v_val_481_);
v___x_483_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_482_);
v___x_484_ = 13ULL;
v___x_485_ = lean_uint64_mix_hash(v___x_483_, v___x_484_);
v___x_486_ = lean_uint64_mix_hash(v___x_478_, v___x_485_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_489_, lean_object* v_x_490_){
_start:
{
uint8_t v_pu_91__boxed_491_; uint64_t v_res_492_; lean_object* v_r_493_; 
v_pu_91__boxed_491_ = lean_unbox(v_pu_489_);
v_res_492_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_91__boxed_491_, v_x_490_);
lean_dec_ref(v_x_490_);
v_r_493_ = lean_box_uint64(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(v_pu_494_);
v___x_496_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* v_pu_497_){
_start:
{
uint8_t v_pu_5__boxed_498_; lean_object* v_res_499_; 
v_pu_5__boxed_498_ = lean_unbox(v_pu_497_);
v_res_499_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_498_);
return v_res_499_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
