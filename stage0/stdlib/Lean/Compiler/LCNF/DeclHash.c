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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
size_t v___x_118_; size_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; 
v___x_118_ = ((size_t)0ULL);
v___x_119_ = lean_usize_of_nat(v___x_115_);
v___x_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_111_, v___x_118_, v___x_119_, v___x_113_);
v___x_121_ = lean_uint64_mix_hash(v___x_112_, v___x_120_);
return v___x_121_;
}
}
case 4:
{
lean_object* v_cases_122_; lean_object* v_resultType_123_; lean_object* v_discr_124_; lean_object* v_alts_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; 
v_cases_122_ = lean_ctor_get(v_code_97_, 0);
v_resultType_123_ = lean_ctor_get(v_cases_122_, 1);
v_discr_124_ = lean_ctor_get(v_cases_122_, 2);
v_alts_125_ = lean_ctor_get(v_cases_122_, 3);
v___x_126_ = l_Lean_instHashableFVarId_hash(v_discr_124_);
v___x_127_ = l_Lean_Expr_hash(v_resultType_123_);
v___x_128_ = lean_uint64_mix_hash(v___x_126_, v___x_127_);
v___x_129_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_96_, v_alts_125_);
v___x_130_ = lean_uint64_mix_hash(v___x_128_, v___x_129_);
return v___x_130_;
}
case 5:
{
lean_object* v_fvarId_131_; uint64_t v___x_132_; 
v_fvarId_131_ = lean_ctor_get(v_code_97_, 0);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_fvarId_131_);
return v___x_132_;
}
case 6:
{
lean_object* v_type_133_; uint64_t v___x_134_; 
v_type_133_ = lean_ctor_get(v_code_97_, 0);
v___x_134_ = l_Lean_Expr_hash(v_type_133_);
return v___x_134_;
}
case 7:
{
lean_object* v_fvarId_135_; lean_object* v_i_136_; lean_object* v_y_137_; lean_object* v_k_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; 
v_fvarId_135_ = lean_ctor_get(v_code_97_, 0);
v_i_136_ = lean_ctor_get(v_code_97_, 1);
v_y_137_ = lean_ctor_get(v_code_97_, 2);
v_k_138_ = lean_ctor_get(v_code_97_, 3);
v___x_139_ = l_Lean_instHashableFVarId_hash(v_fvarId_135_);
v___x_140_ = lean_uint64_of_nat(v_i_136_);
v___x_141_ = lean_uint64_mix_hash(v___x_139_, v___x_140_);
v___x_142_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_137_);
v___x_143_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_138_);
v___x_144_ = lean_uint64_mix_hash(v___x_142_, v___x_143_);
v___x_145_ = lean_uint64_mix_hash(v___x_141_, v___x_144_);
return v___x_145_;
}
case 8:
{
lean_object* v_fvarId_146_; lean_object* v_i_147_; lean_object* v_y_148_; lean_object* v_k_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; 
v_fvarId_146_ = lean_ctor_get(v_code_97_, 0);
v_i_147_ = lean_ctor_get(v_code_97_, 1);
v_y_148_ = lean_ctor_get(v_code_97_, 2);
v_k_149_ = lean_ctor_get(v_code_97_, 3);
v___x_150_ = l_Lean_instHashableFVarId_hash(v_fvarId_146_);
v___x_151_ = lean_uint64_of_nat(v_i_147_);
v___x_152_ = lean_uint64_mix_hash(v___x_150_, v___x_151_);
v___x_153_ = l_Lean_instHashableFVarId_hash(v_y_148_);
v___x_154_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_149_);
v___x_155_ = lean_uint64_mix_hash(v___x_153_, v___x_154_);
v___x_156_ = lean_uint64_mix_hash(v___x_152_, v___x_155_);
return v___x_156_;
}
case 9:
{
lean_object* v_fvarId_157_; lean_object* v_i_158_; lean_object* v_offset_159_; lean_object* v_y_160_; lean_object* v_ty_161_; lean_object* v_k_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; 
v_fvarId_157_ = lean_ctor_get(v_code_97_, 0);
v_i_158_ = lean_ctor_get(v_code_97_, 1);
v_offset_159_ = lean_ctor_get(v_code_97_, 2);
v_y_160_ = lean_ctor_get(v_code_97_, 3);
v_ty_161_ = lean_ctor_get(v_code_97_, 4);
v_k_162_ = lean_ctor_get(v_code_97_, 5);
v___x_163_ = l_Lean_instHashableFVarId_hash(v_fvarId_157_);
v___x_164_ = lean_uint64_of_nat(v_i_158_);
v___x_165_ = lean_uint64_mix_hash(v___x_163_, v___x_164_);
v___x_166_ = lean_uint64_of_nat(v_offset_159_);
v___x_167_ = l_Lean_instHashableFVarId_hash(v_y_160_);
v___x_168_ = lean_uint64_mix_hash(v___x_166_, v___x_167_);
v___x_169_ = l_Lean_Expr_hash(v_ty_161_);
v___x_170_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_162_);
v___x_171_ = lean_uint64_mix_hash(v___x_169_, v___x_170_);
v___x_172_ = lean_uint64_mix_hash(v___x_168_, v___x_171_);
v___x_173_ = lean_uint64_mix_hash(v___x_165_, v___x_172_);
return v___x_173_;
}
case 10:
{
lean_object* v_fvarId_174_; lean_object* v_cidx_175_; lean_object* v_k_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; 
v_fvarId_174_ = lean_ctor_get(v_code_97_, 0);
v_cidx_175_ = lean_ctor_get(v_code_97_, 1);
v_k_176_ = lean_ctor_get(v_code_97_, 2);
v___x_177_ = l_Lean_instHashableFVarId_hash(v_fvarId_174_);
v___x_178_ = lean_uint64_of_nat(v_cidx_175_);
v___x_179_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_176_);
v___x_180_ = lean_uint64_mix_hash(v___x_178_, v___x_179_);
v___x_181_ = lean_uint64_mix_hash(v___x_177_, v___x_180_);
return v___x_181_;
}
case 11:
{
lean_object* v_fvarId_182_; lean_object* v_n_183_; uint8_t v_check_184_; uint8_t v_persistent_185_; lean_object* v_k_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___y_191_; uint64_t v___y_192_; uint64_t v___y_198_; 
v_fvarId_182_ = lean_ctor_get(v_code_97_, 0);
v_n_183_ = lean_ctor_get(v_code_97_, 1);
v_check_184_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3);
v_persistent_185_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3 + 1);
v_k_186_ = lean_ctor_get(v_code_97_, 2);
v___x_187_ = l_Lean_instHashableFVarId_hash(v_fvarId_182_);
v___x_188_ = lean_uint64_of_nat(v_n_183_);
v___x_189_ = lean_uint64_mix_hash(v___x_187_, v___x_188_);
if (v_persistent_185_ == 0)
{
uint64_t v___x_201_; 
v___x_201_ = 13ULL;
v___y_198_ = v___x_201_;
goto v___jp_197_;
}
else
{
uint64_t v___x_202_; 
v___x_202_ = 11ULL;
v___y_198_ = v___x_202_;
goto v___jp_197_;
}
v___jp_190_:
{
uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; 
v___x_193_ = lean_uint64_mix_hash(v___y_191_, v___y_192_);
v___x_194_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_186_);
v___x_195_ = lean_uint64_mix_hash(v___x_193_, v___x_194_);
v___x_196_ = lean_uint64_mix_hash(v___x_189_, v___x_195_);
return v___x_196_;
}
v___jp_197_:
{
if (v_check_184_ == 0)
{
uint64_t v___x_199_; 
v___x_199_ = 13ULL;
v___y_191_ = v___y_198_;
v___y_192_ = v___x_199_;
goto v___jp_190_;
}
else
{
uint64_t v___x_200_; 
v___x_200_ = 11ULL;
v___y_191_ = v___y_198_;
v___y_192_ = v___x_200_;
goto v___jp_190_;
}
}
}
case 12:
{
lean_object* v_fvarId_203_; lean_object* v_n_204_; uint8_t v_check_205_; uint8_t v_persistent_206_; lean_object* v_objs_x3f_207_; lean_object* v_k_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___y_213_; uint64_t v___y_214_; uint64_t v___y_220_; uint64_t v___y_221_; uint64_t v___y_229_; 
v_fvarId_203_ = lean_ctor_get(v_code_97_, 0);
v_n_204_ = lean_ctor_get(v_code_97_, 1);
v_check_205_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*4);
v_persistent_206_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*4 + 1);
v_objs_x3f_207_ = lean_ctor_get(v_code_97_, 2);
v_k_208_ = lean_ctor_get(v_code_97_, 3);
v___x_209_ = l_Lean_instHashableFVarId_hash(v_fvarId_203_);
v___x_210_ = lean_uint64_of_nat(v_n_204_);
v___x_211_ = lean_uint64_mix_hash(v___x_209_, v___x_210_);
if (v_persistent_206_ == 0)
{
uint64_t v___x_232_; 
v___x_232_ = 13ULL;
v___y_229_ = v___x_232_;
goto v___jp_228_;
}
else
{
uint64_t v___x_233_; 
v___x_233_ = 11ULL;
v___y_229_ = v___x_233_;
goto v___jp_228_;
}
v___jp_212_:
{
uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; 
v___x_215_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_208_);
v___x_216_ = lean_uint64_mix_hash(v___y_214_, v___x_215_);
v___x_217_ = lean_uint64_mix_hash(v___y_213_, v___x_216_);
v___x_218_ = lean_uint64_mix_hash(v___x_211_, v___x_217_);
return v___x_218_;
}
v___jp_219_:
{
uint64_t v___x_222_; 
v___x_222_ = lean_uint64_mix_hash(v___y_220_, v___y_221_);
if (lean_obj_tag(v_objs_x3f_207_) == 0)
{
uint64_t v___x_223_; 
v___x_223_ = 11ULL;
v___y_213_ = v___x_222_;
v___y_214_ = v___x_223_;
goto v___jp_212_;
}
else
{
lean_object* v_val_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; 
v_val_224_ = lean_ctor_get(v_objs_x3f_207_, 0);
v___x_225_ = lean_uint64_of_nat(v_val_224_);
v___x_226_ = 13ULL;
v___x_227_ = lean_uint64_mix_hash(v___x_225_, v___x_226_);
v___y_213_ = v___x_222_;
v___y_214_ = v___x_227_;
goto v___jp_212_;
}
}
v___jp_228_:
{
if (v_check_205_ == 0)
{
uint64_t v___x_230_; 
v___x_230_ = 13ULL;
v___y_220_ = v___y_229_;
v___y_221_ = v___x_230_;
goto v___jp_219_;
}
else
{
uint64_t v___x_231_; 
v___x_231_ = 11ULL;
v___y_220_ = v___y_229_;
v___y_221_ = v___x_231_;
goto v___jp_219_;
}
}
}
case 13:
{
lean_object* v_fvarId_234_; lean_object* v_k_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; 
v_fvarId_234_ = lean_ctor_get(v_code_97_, 0);
v_k_235_ = lean_ctor_get(v_code_97_, 1);
v___x_236_ = l_Lean_instHashableFVarId_hash(v_fvarId_234_);
v___x_237_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_235_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
return v___x_238_;
}
default: 
{
lean_object* v_decl_239_; lean_object* v_k_240_; lean_object* v_fvarId_241_; lean_object* v_params_242_; lean_object* v_type_243_; lean_object* v_value_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_decl_239_ = lean_ctor_get(v_code_97_, 0);
v_k_240_ = lean_ctor_get(v_code_97_, 1);
v_fvarId_241_ = lean_ctor_get(v_decl_239_, 0);
v_params_242_ = lean_ctor_get(v_decl_239_, 2);
v_type_243_ = lean_ctor_get(v_decl_239_, 3);
v_value_244_ = lean_ctor_get(v_decl_239_, 4);
v___x_245_ = l_Lean_instHashableFVarId_hash(v_fvarId_241_);
v___x_246_ = l_Lean_Expr_hash(v_type_243_);
v___x_247_ = lean_uint64_mix_hash(v___x_245_, v___x_246_);
v___x_248_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_value_244_);
v___x_249_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_240_);
v___x_250_ = lean_uint64_mix_hash(v___x_248_, v___x_249_);
v___x_251_ = lean_uint64_mix_hash(v___x_247_, v___x_250_);
v___x_252_ = 7ULL;
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_get_size(v_params_242_);
v___x_255_ = lean_nat_dec_lt(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
uint64_t v___x_256_; 
v___x_256_ = lean_uint64_mix_hash(v___x_251_, v___x_252_);
return v___x_256_;
}
else
{
size_t v___x_257_; size_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; 
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_254_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_242_, v___x_257_, v___x_258_, v___x_252_);
v___x_260_ = lean_uint64_mix_hash(v___x_251_, v___x_259_);
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_261_, lean_object* v_alt_262_){
_start:
{
switch(lean_obj_tag(v_alt_262_))
{
case 0:
{
lean_object* v_ctorName_263_; lean_object* v_params_264_; lean_object* v_code_265_; uint64_t v___y_267_; uint64_t v___y_268_; uint64_t v___y_273_; 
v_ctorName_263_ = lean_ctor_get(v_alt_262_, 0);
v_params_264_ = lean_ctor_get(v_alt_262_, 1);
v_code_265_ = lean_ctor_get(v_alt_262_, 2);
if (lean_obj_tag(v_ctorName_263_) == 0)
{
uint64_t v___x_281_; 
v___x_281_ = 1723ULL;
v___y_273_ = v___x_281_;
goto v___jp_272_;
}
else
{
uint64_t v_hash_282_; 
v_hash_282_ = lean_ctor_get_uint64(v_ctorName_263_, sizeof(void*)*2);
v___y_273_ = v_hash_282_;
goto v___jp_272_;
}
v___jp_266_:
{
uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; 
v___x_269_ = lean_uint64_mix_hash(v___y_267_, v___y_268_);
v___x_270_ = l_Lean_Compiler_LCNF_hashCode(v_pu_261_, v_code_265_);
v___x_271_ = lean_uint64_mix_hash(v___x_269_, v___x_270_);
return v___x_271_;
}
v___jp_272_:
{
uint64_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_274_ = 7ULL;
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_array_get_size(v_params_264_);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
v___y_267_ = v___y_273_;
v___y_268_ = v___x_274_;
goto v___jp_266_;
}
else
{
size_t v___x_278_; size_t v___x_279_; uint64_t v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_276_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_264_, v___x_278_, v___x_279_, v___x_274_);
v___y_267_ = v___y_273_;
v___y_268_ = v___x_280_;
goto v___jp_266_;
}
}
}
case 1:
{
lean_object* v_info_283_; lean_object* v_code_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; 
v_info_283_ = lean_ctor_get(v_alt_262_, 0);
v_code_284_ = lean_ctor_get(v_alt_262_, 1);
v___x_285_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_283_);
v___x_286_ = l_Lean_Compiler_LCNF_hashCode(v_pu_261_, v_code_284_);
v___x_287_ = lean_uint64_mix_hash(v___x_285_, v___x_286_);
return v___x_287_;
}
default: 
{
lean_object* v_code_288_; uint64_t v___x_289_; 
v_code_288_ = lean_ctor_get(v_alt_262_, 0);
v___x_289_ = l_Lean_Compiler_LCNF_hashCode(v_pu_261_, v_code_288_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_290_, lean_object* v_as_291_, size_t v_i_292_, size_t v_stop_293_, uint64_t v_b_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_eq(v_i_292_, v_stop_293_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; 
v___x_296_ = lean_array_uget_borrowed(v_as_291_, v_i_292_);
v___x_297_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_290_, v___x_296_);
v___x_298_ = lean_uint64_mix_hash(v_b_294_, v___x_297_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_292_, v___x_299_);
v_i_292_ = v___x_300_;
v_b_294_ = v___x_298_;
goto _start;
}
else
{
return v_b_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_302_, lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_, lean_object* v_b_306_){
_start:
{
uint8_t v_pu_boxed_307_; size_t v_i_boxed_308_; size_t v_stop_boxed_309_; uint64_t v_b_boxed_310_; uint64_t v_res_311_; lean_object* v_r_312_; 
v_pu_boxed_307_ = lean_unbox(v_pu_302_);
v_i_boxed_308_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_309_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_b_boxed_310_ = lean_unbox_uint64(v_b_306_);
lean_dec_ref(v_b_306_);
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_307_, v_as_303_, v_i_boxed_308_, v_stop_boxed_309_, v_b_boxed_310_);
lean_dec_ref(v_as_303_);
v_r_312_ = lean_box_uint64(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_313_, lean_object* v_alts_314_){
_start:
{
uint8_t v_pu_boxed_315_; uint64_t v_res_316_; lean_object* v_r_317_; 
v_pu_boxed_315_ = lean_unbox(v_pu_313_);
v_res_316_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_315_, v_alts_314_);
lean_dec_ref(v_alts_314_);
v_r_317_ = lean_box_uint64(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_318_, lean_object* v_alt_319_){
_start:
{
uint8_t v_pu_boxed_320_; uint64_t v_res_321_; lean_object* v_r_322_; 
v_pu_boxed_320_ = lean_unbox(v_pu_318_);
v_res_321_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_320_, v_alt_319_);
lean_dec_ref(v_alt_319_);
v_r_322_ = lean_box_uint64(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_323_, lean_object* v_code_324_){
_start:
{
uint8_t v_pu_boxed_325_; uint64_t v_res_326_; lean_object* v_r_327_; 
v_pu_boxed_325_ = lean_unbox(v_pu_323_);
v_res_326_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_325_, v_code_324_);
lean_dec_ref(v_code_324_);
v_r_327_ = lean_box_uint64(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_328_, lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, uint64_t v_b_332_){
_start:
{
uint64_t v___x_333_; 
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_329_, v_i_330_, v_stop_331_, v_b_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_334_, lean_object* v_as_335_, lean_object* v_i_336_, lean_object* v_stop_337_, lean_object* v_b_338_){
_start:
{
uint8_t v_pu_boxed_339_; size_t v_i_boxed_340_; size_t v_stop_boxed_341_; uint64_t v_b_boxed_342_; uint64_t v_res_343_; lean_object* v_r_344_; 
v_pu_boxed_339_ = lean_unbox(v_pu_334_);
v_i_boxed_340_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_stop_boxed_341_ = lean_unbox_usize(v_stop_337_);
lean_dec(v_stop_337_);
v_b_boxed_342_ = lean_unbox_uint64(v_b_338_);
lean_dec_ref(v_b_338_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_339_, v_as_335_, v_i_boxed_340_, v_stop_boxed_341_, v_b_boxed_342_);
lean_dec_ref(v_as_335_);
v_r_344_ = lean_box_uint64(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_345_, lean_object* v_c_346_){
_start:
{
uint64_t v___x_347_; 
v___x_347_ = l_Lean_Compiler_LCNF_hashCode(v_pu_345_, v_c_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_348_, lean_object* v_c_349_){
_start:
{
uint8_t v_pu_boxed_350_; uint64_t v_res_351_; lean_object* v_r_352_; 
v_pu_boxed_350_ = lean_unbox(v_pu_348_);
v_res_351_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_350_, v_c_349_);
lean_dec_ref(v_c_349_);
v_r_352_ = lean_box_uint64(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___f_355_; 
v___x_354_ = lean_box(v_pu_353_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_355_, 0, v___x_354_);
return v___f_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_356_){
_start:
{
uint8_t v_pu_boxed_357_; lean_object* v_res_358_; 
v_pu_boxed_357_ = lean_unbox(v_pu_356_);
v_res_358_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_357_);
return v_res_358_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_code_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; 
v_code_361_ = lean_ctor_get(v_x_360_, 0);
v___x_362_ = 0ULL;
v___x_363_ = l_Lean_Compiler_LCNF_hashCode(v_pu_359_, v_code_361_);
v___x_364_ = lean_uint64_mix_hash(v___x_362_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_externAttrData_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; 
v_externAttrData_365_ = lean_ctor_get(v_x_360_, 0);
v___x_366_ = 1ULL;
v___x_367_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_365_);
v___x_368_ = lean_uint64_mix_hash(v___x_366_, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_pu_47__boxed_371_; uint64_t v_res_372_; lean_object* v_r_373_; 
v_pu_47__boxed_371_ = lean_unbox(v_pu_369_);
v_res_372_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_371_, v_x_370_);
lean_dec_ref(v_x_370_);
v_r_373_ = lean_box_uint64(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_box(v_pu_374_);
v___x_376_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* v_pu_377_){
_start:
{
uint8_t v_pu_5__boxed_378_; lean_object* v_res_379_; 
v_pu_5__boxed_378_ = lean_unbox(v_pu_377_);
v_res_379_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_378_);
return v_res_379_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
return v_x_380_;
}
else
{
lean_object* v_head_382_; lean_object* v_tail_383_; uint64_t v___y_385_; 
v_head_382_ = lean_ctor_get(v_x_381_, 0);
v_tail_383_ = lean_ctor_get(v_x_381_, 1);
if (lean_obj_tag(v_head_382_) == 0)
{
uint64_t v___x_388_; 
v___x_388_ = 1723ULL;
v___y_385_ = v___x_388_;
goto v___jp_384_;
}
else
{
uint64_t v_hash_389_; 
v_hash_389_ = lean_ctor_get_uint64(v_head_382_, sizeof(void*)*2);
v___y_385_ = v_hash_389_;
goto v___jp_384_;
}
v___jp_384_:
{
uint64_t v___x_386_; 
v___x_386_ = lean_uint64_mix_hash(v_x_380_, v___y_385_);
v_x_380_ = v___x_386_;
v_x_381_ = v_tail_383_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint64_t v_x_184__boxed_392_; uint64_t v_res_393_; lean_object* v_r_394_; 
v_x_184__boxed_392_ = lean_unbox_uint64(v_x_390_);
lean_dec_ref(v_x_390_);
v_res_393_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_184__boxed_392_, v_x_391_);
lean_dec(v_x_391_);
v_r_394_ = lean_box_uint64(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_395_){
_start:
{
lean_object* v_name_396_; lean_object* v_levelParams_397_; lean_object* v_type_398_; lean_object* v_params_399_; uint8_t v_safe_400_; uint64_t v___y_402_; uint64_t v___y_403_; uint64_t v___x_409_; uint64_t v___y_411_; 
v_name_396_ = lean_ctor_get(v_x_395_, 0);
v_levelParams_397_ = lean_ctor_get(v_x_395_, 1);
v_type_398_ = lean_ctor_get(v_x_395_, 2);
v_params_399_ = lean_ctor_get(v_x_395_, 3);
v_safe_400_ = lean_ctor_get_uint8(v_x_395_, sizeof(void*)*4);
v___x_409_ = 0ULL;
if (lean_obj_tag(v_name_396_) == 0)
{
uint64_t v___x_424_; 
v___x_424_ = 1723ULL;
v___y_411_ = v___x_424_;
goto v___jp_410_;
}
else
{
uint64_t v_hash_425_; 
v_hash_425_ = lean_ctor_get_uint64(v_name_396_, sizeof(void*)*2);
v___y_411_ = v_hash_425_;
goto v___jp_410_;
}
v___jp_401_:
{
uint64_t v___x_404_; 
v___x_404_ = lean_uint64_mix_hash(v___y_402_, v___y_403_);
if (v_safe_400_ == 0)
{
uint64_t v___x_405_; uint64_t v___x_406_; 
v___x_405_ = 13ULL;
v___x_406_ = lean_uint64_mix_hash(v___x_404_, v___x_405_);
return v___x_406_;
}
else
{
uint64_t v___x_407_; uint64_t v___x_408_; 
v___x_407_ = 11ULL;
v___x_408_ = lean_uint64_mix_hash(v___x_404_, v___x_407_);
return v___x_408_;
}
}
v___jp_410_:
{
uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_412_ = lean_uint64_mix_hash(v___x_409_, v___y_411_);
v___x_413_ = 7ULL;
v___x_414_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_413_, v_levelParams_397_);
v___x_415_ = lean_uint64_mix_hash(v___x_412_, v___x_414_);
v___x_416_ = l_Lean_Expr_hash(v_type_398_);
v___x_417_ = lean_uint64_mix_hash(v___x_415_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_array_get_size(v_params_399_);
v___x_420_ = lean_nat_dec_lt(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
v___y_402_ = v___x_417_;
v___y_403_ = v___x_413_;
goto v___jp_401_;
}
else
{
size_t v___x_421_; size_t v___x_422_; uint64_t v___x_423_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_419_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_399_, v___x_421_, v___x_422_, v___x_413_);
v___y_402_ = v___x_417_;
v___y_403_ = v___x_423_;
goto v___jp_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_426_){
_start:
{
uint64_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_426_);
lean_dec_ref(v_x_426_);
v_r_428_ = lean_box_uint64(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_429_, lean_object* v_x_430_){
_start:
{
uint64_t v___x_431_; 
v___x_431_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_pu_265__boxed_434_; uint64_t v_res_435_; lean_object* v_r_436_; 
v_pu_265__boxed_434_ = lean_unbox(v_pu_432_);
v_res_435_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_265__boxed_434_, v_x_433_);
lean_dec_ref(v_x_433_);
v_r_436_ = lean_box_uint64(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(v_pu_437_);
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* v_pu_440_){
_start:
{
uint8_t v_pu_5__boxed_441_; lean_object* v_res_442_; 
v_pu_5__boxed_441_ = lean_unbox(v_pu_440_);
v_res_442_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_toSignature_445_; lean_object* v_value_446_; uint8_t v_recursive_447_; lean_object* v_inlineAttr_x3f_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___y_455_; 
v_toSignature_445_ = lean_ctor_get(v_x_444_, 0);
v_value_446_ = lean_ctor_get(v_x_444_, 1);
v_recursive_447_ = lean_ctor_get_uint8(v_x_444_, sizeof(void*)*3);
v_inlineAttr_x3f_448_ = lean_ctor_get(v_x_444_, 2);
v___x_449_ = 0ULL;
v___x_450_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_445_);
v___x_451_ = lean_uint64_mix_hash(v___x_449_, v___x_450_);
v___x_452_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_443_, v_value_446_);
v___x_453_ = lean_uint64_mix_hash(v___x_451_, v___x_452_);
if (v_recursive_447_ == 0)
{
uint64_t v___x_465_; 
v___x_465_ = 13ULL;
v___y_455_ = v___x_465_;
goto v___jp_454_;
}
else
{
uint64_t v___x_466_; 
v___x_466_ = 11ULL;
v___y_455_ = v___x_466_;
goto v___jp_454_;
}
v___jp_454_:
{
uint64_t v___x_456_; 
v___x_456_ = lean_uint64_mix_hash(v___x_453_, v___y_455_);
if (lean_obj_tag(v_inlineAttr_x3f_448_) == 0)
{
uint64_t v___x_457_; uint64_t v___x_458_; 
v___x_457_ = 11ULL;
v___x_458_ = lean_uint64_mix_hash(v___x_456_, v___x_457_);
return v___x_458_;
}
else
{
lean_object* v_val_459_; uint8_t v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; 
v_val_459_ = lean_ctor_get(v_inlineAttr_x3f_448_, 0);
v___x_460_ = lean_unbox(v_val_459_);
v___x_461_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_460_);
v___x_462_ = 13ULL;
v___x_463_ = lean_uint64_mix_hash(v___x_461_, v___x_462_);
v___x_464_ = lean_uint64_mix_hash(v___x_456_, v___x_463_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_467_, lean_object* v_x_468_){
_start:
{
uint8_t v_pu_92__boxed_469_; uint64_t v_res_470_; lean_object* v_r_471_; 
v_pu_92__boxed_469_ = lean_unbox(v_pu_467_);
v_res_470_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_92__boxed_469_, v_x_468_);
lean_dec_ref(v_x_468_);
v_r_471_ = lean_box_uint64(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_box(v_pu_472_);
v___x_474_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* v_pu_475_){
_start:
{
uint8_t v_pu_5__boxed_476_; lean_object* v_res_477_; 
v_pu_5__boxed_476_ = lean_unbox(v_pu_475_);
v_res_477_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_476_);
return v_res_477_;
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
