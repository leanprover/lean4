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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(lean_object*);
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
uint64_t v___y_99_; lean_object* v___y_100_; uint64_t v___y_101_; uint64_t v___y_102_; uint8_t v___y_108_; uint64_t v___y_109_; lean_object* v___y_110_; uint64_t v___y_111_; lean_object* v_fvarId_115_; lean_object* v_n_116_; uint8_t v_check_117_; uint8_t v_persistent_118_; lean_object* v_k_119_; 
switch(lean_obj_tag(v_code_97_))
{
case 0:
{
lean_object* v_decl_125_; lean_object* v_k_126_; lean_object* v_fvarId_127_; lean_object* v_type_128_; lean_object* v_value_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; 
v_decl_125_ = lean_ctor_get(v_code_97_, 0);
v_k_126_ = lean_ctor_get(v_code_97_, 1);
v_fvarId_127_ = lean_ctor_get(v_decl_125_, 0);
v_type_128_ = lean_ctor_get(v_decl_125_, 2);
v_value_129_ = lean_ctor_get(v_decl_125_, 3);
v___x_130_ = l_Lean_instHashableFVarId_hash(v_fvarId_127_);
v___x_131_ = l_Lean_Expr_hash(v_type_128_);
v___x_132_ = lean_uint64_mix_hash(v___x_130_, v___x_131_);
v___x_133_ = l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_96_, v_value_129_);
v___x_134_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_126_);
v___x_135_ = lean_uint64_mix_hash(v___x_133_, v___x_134_);
v___x_136_ = lean_uint64_mix_hash(v___x_132_, v___x_135_);
return v___x_136_;
}
case 3:
{
lean_object* v_fvarId_137_; lean_object* v_args_138_; uint64_t v___x_139_; uint64_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_fvarId_137_ = lean_ctor_get(v_code_97_, 0);
v_args_138_ = lean_ctor_get(v_code_97_, 1);
v___x_139_ = l_Lean_instHashableFVarId_hash(v_fvarId_137_);
v___x_140_ = 7ULL;
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_args_138_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
uint64_t v___x_144_; 
v___x_144_ = lean_uint64_mix_hash(v___x_139_, v___x_140_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_142_);
if (v___x_145_ == 0)
{
if (v___x_143_ == 0)
{
uint64_t v___x_146_; 
v___x_146_ = lean_uint64_mix_hash(v___x_139_, v___x_140_);
return v___x_146_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_142_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_138_, v___x_147_, v___x_148_, v___x_140_);
v___x_150_ = lean_uint64_mix_hash(v___x_139_, v___x_149_);
return v___x_150_;
}
}
else
{
size_t v___x_151_; size_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; 
v___x_151_ = ((size_t)0ULL);
v___x_152_ = lean_usize_of_nat(v___x_142_);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_138_, v___x_151_, v___x_152_, v___x_140_);
v___x_154_ = lean_uint64_mix_hash(v___x_139_, v___x_153_);
return v___x_154_;
}
}
}
case 4:
{
lean_object* v_cases_155_; lean_object* v_resultType_156_; lean_object* v_discr_157_; lean_object* v_alts_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; 
v_cases_155_ = lean_ctor_get(v_code_97_, 0);
v_resultType_156_ = lean_ctor_get(v_cases_155_, 1);
v_discr_157_ = lean_ctor_get(v_cases_155_, 2);
v_alts_158_ = lean_ctor_get(v_cases_155_, 3);
v___x_159_ = l_Lean_instHashableFVarId_hash(v_discr_157_);
v___x_160_ = l_Lean_Expr_hash(v_resultType_156_);
v___x_161_ = lean_uint64_mix_hash(v___x_159_, v___x_160_);
v___x_162_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_96_, v_alts_158_);
v___x_163_ = lean_uint64_mix_hash(v___x_161_, v___x_162_);
return v___x_163_;
}
case 5:
{
lean_object* v_fvarId_164_; uint64_t v___x_165_; 
v_fvarId_164_ = lean_ctor_get(v_code_97_, 0);
v___x_165_ = l_Lean_instHashableFVarId_hash(v_fvarId_164_);
return v___x_165_;
}
case 6:
{
lean_object* v_type_166_; uint64_t v___x_167_; 
v_type_166_ = lean_ctor_get(v_code_97_, 0);
v___x_167_ = l_Lean_Expr_hash(v_type_166_);
return v___x_167_;
}
case 7:
{
lean_object* v_fvarId_168_; lean_object* v_i_169_; lean_object* v_y_170_; lean_object* v_k_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; 
v_fvarId_168_ = lean_ctor_get(v_code_97_, 0);
v_i_169_ = lean_ctor_get(v_code_97_, 1);
v_y_170_ = lean_ctor_get(v_code_97_, 2);
v_k_171_ = lean_ctor_get(v_code_97_, 3);
v___x_172_ = l_Lean_instHashableFVarId_hash(v_fvarId_168_);
v___x_173_ = lean_uint64_of_nat(v_i_169_);
v___x_174_ = lean_uint64_mix_hash(v___x_172_, v___x_173_);
v___x_175_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_170_);
v___x_176_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_171_);
v___x_177_ = lean_uint64_mix_hash(v___x_175_, v___x_176_);
v___x_178_ = lean_uint64_mix_hash(v___x_174_, v___x_177_);
return v___x_178_;
}
case 8:
{
lean_object* v_fvarId_179_; lean_object* v_i_180_; lean_object* v_y_181_; lean_object* v_k_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; 
v_fvarId_179_ = lean_ctor_get(v_code_97_, 0);
v_i_180_ = lean_ctor_get(v_code_97_, 1);
v_y_181_ = lean_ctor_get(v_code_97_, 2);
v_k_182_ = lean_ctor_get(v_code_97_, 3);
v___x_183_ = l_Lean_instHashableFVarId_hash(v_fvarId_179_);
v___x_184_ = lean_uint64_of_nat(v_i_180_);
v___x_185_ = lean_uint64_mix_hash(v___x_183_, v___x_184_);
v___x_186_ = l_Lean_instHashableFVarId_hash(v_y_181_);
v___x_187_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_182_);
v___x_188_ = lean_uint64_mix_hash(v___x_186_, v___x_187_);
v___x_189_ = lean_uint64_mix_hash(v___x_185_, v___x_188_);
return v___x_189_;
}
case 9:
{
lean_object* v_fvarId_190_; lean_object* v_i_191_; lean_object* v_offset_192_; lean_object* v_y_193_; lean_object* v_ty_194_; lean_object* v_k_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; uint64_t v___x_206_; 
v_fvarId_190_ = lean_ctor_get(v_code_97_, 0);
v_i_191_ = lean_ctor_get(v_code_97_, 1);
v_offset_192_ = lean_ctor_get(v_code_97_, 2);
v_y_193_ = lean_ctor_get(v_code_97_, 3);
v_ty_194_ = lean_ctor_get(v_code_97_, 4);
v_k_195_ = lean_ctor_get(v_code_97_, 5);
v___x_196_ = l_Lean_instHashableFVarId_hash(v_fvarId_190_);
v___x_197_ = lean_uint64_of_nat(v_i_191_);
v___x_198_ = lean_uint64_mix_hash(v___x_196_, v___x_197_);
v___x_199_ = lean_uint64_of_nat(v_offset_192_);
v___x_200_ = l_Lean_instHashableFVarId_hash(v_y_193_);
v___x_201_ = lean_uint64_mix_hash(v___x_199_, v___x_200_);
v___x_202_ = l_Lean_Expr_hash(v_ty_194_);
v___x_203_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_195_);
v___x_204_ = lean_uint64_mix_hash(v___x_202_, v___x_203_);
v___x_205_ = lean_uint64_mix_hash(v___x_201_, v___x_204_);
v___x_206_ = lean_uint64_mix_hash(v___x_198_, v___x_205_);
return v___x_206_;
}
case 10:
{
lean_object* v_fvarId_207_; lean_object* v_cidx_208_; lean_object* v_k_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; 
v_fvarId_207_ = lean_ctor_get(v_code_97_, 0);
v_cidx_208_ = lean_ctor_get(v_code_97_, 1);
v_k_209_ = lean_ctor_get(v_code_97_, 2);
v___x_210_ = l_Lean_instHashableFVarId_hash(v_fvarId_207_);
v___x_211_ = lean_uint64_of_nat(v_cidx_208_);
v___x_212_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_209_);
v___x_213_ = lean_uint64_mix_hash(v___x_211_, v___x_212_);
v___x_214_ = lean_uint64_mix_hash(v___x_210_, v___x_213_);
return v___x_214_;
}
case 11:
{
lean_object* v_fvarId_215_; lean_object* v_n_216_; uint8_t v_check_217_; uint8_t v_persistent_218_; lean_object* v_k_219_; 
v_fvarId_215_ = lean_ctor_get(v_code_97_, 0);
v_n_216_ = lean_ctor_get(v_code_97_, 1);
v_check_217_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3);
v_persistent_218_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3 + 1);
v_k_219_ = lean_ctor_get(v_code_97_, 2);
v_fvarId_115_ = v_fvarId_215_;
v_n_116_ = v_n_216_;
v_check_117_ = v_check_217_;
v_persistent_118_ = v_persistent_218_;
v_k_119_ = v_k_219_;
goto v___jp_114_;
}
case 12:
{
lean_object* v_fvarId_220_; lean_object* v_n_221_; uint8_t v_check_222_; uint8_t v_persistent_223_; lean_object* v_k_224_; 
v_fvarId_220_ = lean_ctor_get(v_code_97_, 0);
v_n_221_ = lean_ctor_get(v_code_97_, 1);
v_check_222_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3);
v_persistent_223_ = lean_ctor_get_uint8(v_code_97_, sizeof(void*)*3 + 1);
v_k_224_ = lean_ctor_get(v_code_97_, 2);
v_fvarId_115_ = v_fvarId_220_;
v_n_116_ = v_n_221_;
v_check_117_ = v_check_222_;
v_persistent_118_ = v_persistent_223_;
v_k_119_ = v_k_224_;
goto v___jp_114_;
}
case 13:
{
lean_object* v_fvarId_225_; lean_object* v_k_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; 
v_fvarId_225_ = lean_ctor_get(v_code_97_, 0);
v_k_226_ = lean_ctor_get(v_code_97_, 1);
v___x_227_ = l_Lean_instHashableFVarId_hash(v_fvarId_225_);
v___x_228_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_226_);
v___x_229_ = lean_uint64_mix_hash(v___x_227_, v___x_228_);
return v___x_229_;
}
default: 
{
lean_object* v_decl_230_; lean_object* v_k_231_; lean_object* v_fvarId_232_; lean_object* v_params_233_; lean_object* v_type_234_; lean_object* v_value_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_decl_230_ = lean_ctor_get(v_code_97_, 0);
v_k_231_ = lean_ctor_get(v_code_97_, 1);
v_fvarId_232_ = lean_ctor_get(v_decl_230_, 0);
v_params_233_ = lean_ctor_get(v_decl_230_, 2);
v_type_234_ = lean_ctor_get(v_decl_230_, 3);
v_value_235_ = lean_ctor_get(v_decl_230_, 4);
v___x_236_ = l_Lean_instHashableFVarId_hash(v_fvarId_232_);
v___x_237_ = l_Lean_Expr_hash(v_type_234_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
v___x_239_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_value_235_);
v___x_240_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v_k_231_);
v___x_241_ = lean_uint64_mix_hash(v___x_239_, v___x_240_);
v___x_242_ = lean_uint64_mix_hash(v___x_238_, v___x_241_);
v___x_243_ = 7ULL;
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_get_size(v_params_233_);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
uint64_t v___x_247_; 
v___x_247_ = lean_uint64_mix_hash(v___x_242_, v___x_243_);
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = lean_nat_dec_le(v___x_245_, v___x_245_);
if (v___x_248_ == 0)
{
if (v___x_246_ == 0)
{
uint64_t v___x_249_; 
v___x_249_ = lean_uint64_mix_hash(v___x_242_, v___x_243_);
return v___x_249_;
}
else
{
size_t v___x_250_; size_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_245_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_233_, v___x_250_, v___x_251_, v___x_243_);
v___x_253_ = lean_uint64_mix_hash(v___x_242_, v___x_252_);
return v___x_253_;
}
}
else
{
size_t v___x_254_; size_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; 
v___x_254_ = ((size_t)0ULL);
v___x_255_ = lean_usize_of_nat(v___x_245_);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_233_, v___x_254_, v___x_255_, v___x_243_);
v___x_257_ = lean_uint64_mix_hash(v___x_242_, v___x_256_);
return v___x_257_;
}
}
}
}
v___jp_98_:
{
uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; 
v___x_103_ = lean_uint64_mix_hash(v___y_101_, v___y_102_);
v___x_104_ = l_Lean_Compiler_LCNF_hashCode(v_pu_96_, v___y_100_);
v___x_105_ = lean_uint64_mix_hash(v___x_103_, v___x_104_);
v___x_106_ = lean_uint64_mix_hash(v___y_99_, v___x_105_);
return v___x_106_;
}
v___jp_107_:
{
if (v___y_108_ == 0)
{
uint64_t v___x_112_; 
v___x_112_ = 13ULL;
v___y_99_ = v___y_109_;
v___y_100_ = v___y_110_;
v___y_101_ = v___y_111_;
v___y_102_ = v___x_112_;
goto v___jp_98_;
}
else
{
uint64_t v___x_113_; 
v___x_113_ = 11ULL;
v___y_99_ = v___y_109_;
v___y_100_ = v___y_110_;
v___y_101_ = v___y_111_;
v___y_102_ = v___x_113_;
goto v___jp_98_;
}
}
v___jp_114_:
{
uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; 
v___x_120_ = l_Lean_instHashableFVarId_hash(v_fvarId_115_);
v___x_121_ = lean_uint64_of_nat(v_n_116_);
v___x_122_ = lean_uint64_mix_hash(v___x_120_, v___x_121_);
if (v_persistent_118_ == 0)
{
uint64_t v___x_123_; 
v___x_123_ = 13ULL;
v___y_108_ = v_check_117_;
v___y_109_ = v___x_122_;
v___y_110_ = v_k_119_;
v___y_111_ = v___x_123_;
goto v___jp_107_;
}
else
{
uint64_t v___x_124_; 
v___x_124_ = 11ULL;
v___y_108_ = v_check_117_;
v___y_109_ = v___x_122_;
v___y_110_ = v_k_119_;
v___y_111_ = v___x_124_;
goto v___jp_107_;
}
}
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_hashAlt___closed__0(void){
_start:
{
lean_object* v___x_258_; uint64_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1723u);
v___x_259_ = lean_uint64_of_nat(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_260_, lean_object* v_alt_261_){
_start:
{
switch(lean_obj_tag(v_alt_261_))
{
case 0:
{
lean_object* v_ctorName_262_; lean_object* v_params_263_; lean_object* v_code_264_; uint64_t v___y_266_; uint64_t v___y_267_; uint64_t v___y_272_; 
v_ctorName_262_ = lean_ctor_get(v_alt_261_, 0);
v_params_263_ = lean_ctor_get(v_alt_261_, 1);
v_code_264_ = lean_ctor_get(v_alt_261_, 2);
if (lean_obj_tag(v_ctorName_262_) == 0)
{
uint64_t v___x_284_; 
v___x_284_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_272_ = v___x_284_;
goto v___jp_271_;
}
else
{
uint64_t v_hash_285_; 
v_hash_285_ = lean_ctor_get_uint64(v_ctorName_262_, sizeof(void*)*2);
v___y_272_ = v_hash_285_;
goto v___jp_271_;
}
v___jp_265_:
{
uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; 
v___x_268_ = lean_uint64_mix_hash(v___y_266_, v___y_267_);
v___x_269_ = l_Lean_Compiler_LCNF_hashCode(v_pu_260_, v_code_264_);
v___x_270_ = lean_uint64_mix_hash(v___x_268_, v___x_269_);
return v___x_270_;
}
v___jp_271_:
{
uint64_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_273_ = 7ULL;
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_array_get_size(v_params_263_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
v___y_266_ = v___y_272_;
v___y_267_ = v___x_273_;
goto v___jp_265_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = lean_nat_dec_le(v___x_275_, v___x_275_);
if (v___x_277_ == 0)
{
if (v___x_276_ == 0)
{
v___y_266_ = v___y_272_;
v___y_267_ = v___x_273_;
goto v___jp_265_;
}
else
{
size_t v___x_278_; size_t v___x_279_; uint64_t v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_275_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_263_, v___x_278_, v___x_279_, v___x_273_);
v___y_266_ = v___y_272_;
v___y_267_ = v___x_280_;
goto v___jp_265_;
}
}
else
{
size_t v___x_281_; size_t v___x_282_; uint64_t v___x_283_; 
v___x_281_ = ((size_t)0ULL);
v___x_282_ = lean_usize_of_nat(v___x_275_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_263_, v___x_281_, v___x_282_, v___x_273_);
v___y_266_ = v___y_272_;
v___y_267_ = v___x_283_;
goto v___jp_265_;
}
}
}
}
case 1:
{
lean_object* v_info_286_; lean_object* v_code_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; 
v_info_286_ = lean_ctor_get(v_alt_261_, 0);
v_code_287_ = lean_ctor_get(v_alt_261_, 1);
v___x_288_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_286_);
v___x_289_ = l_Lean_Compiler_LCNF_hashCode(v_pu_260_, v_code_287_);
v___x_290_ = lean_uint64_mix_hash(v___x_288_, v___x_289_);
return v___x_290_;
}
default: 
{
lean_object* v_code_291_; uint64_t v___x_292_; 
v_code_291_ = lean_ctor_get(v_alt_261_, 0);
v___x_292_ = l_Lean_Compiler_LCNF_hashCode(v_pu_260_, v_code_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_293_, lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_, uint64_t v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; uint64_t v___x_300_; uint64_t v___x_301_; size_t v___x_302_; size_t v___x_303_; 
v___x_299_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
v___x_300_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_293_, v___x_299_);
v___x_301_ = lean_uint64_mix_hash(v_b_297_, v___x_300_);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_add(v_i_295_, v___x_302_);
v_i_295_ = v___x_303_;
v_b_297_ = v___x_301_;
goto _start;
}
else
{
return v_b_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_305_, lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_stop_308_, lean_object* v_b_309_){
_start:
{
uint8_t v_pu_boxed_310_; size_t v_i_boxed_311_; size_t v_stop_boxed_312_; uint64_t v_b_boxed_313_; uint64_t v_res_314_; lean_object* v_r_315_; 
v_pu_boxed_310_ = lean_unbox(v_pu_305_);
v_i_boxed_311_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_stop_boxed_312_ = lean_unbox_usize(v_stop_308_);
lean_dec(v_stop_308_);
v_b_boxed_313_ = lean_unbox_uint64(v_b_309_);
lean_dec_ref(v_b_309_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_310_, v_as_306_, v_i_boxed_311_, v_stop_boxed_312_, v_b_boxed_313_);
lean_dec_ref(v_as_306_);
v_r_315_ = lean_box_uint64(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_316_, lean_object* v_alts_317_){
_start:
{
uint8_t v_pu_boxed_318_; uint64_t v_res_319_; lean_object* v_r_320_; 
v_pu_boxed_318_ = lean_unbox(v_pu_316_);
v_res_319_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_318_, v_alts_317_);
lean_dec_ref(v_alts_317_);
v_r_320_ = lean_box_uint64(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_321_, lean_object* v_alt_322_){
_start:
{
uint8_t v_pu_boxed_323_; uint64_t v_res_324_; lean_object* v_r_325_; 
v_pu_boxed_323_ = lean_unbox(v_pu_321_);
v_res_324_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_323_, v_alt_322_);
lean_dec_ref(v_alt_322_);
v_r_325_ = lean_box_uint64(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_326_, lean_object* v_code_327_){
_start:
{
uint8_t v_pu_boxed_328_; uint64_t v_res_329_; lean_object* v_r_330_; 
v_pu_boxed_328_ = lean_unbox(v_pu_326_);
v_res_329_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_328_, v_code_327_);
lean_dec_ref(v_code_327_);
v_r_330_ = lean_box_uint64(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_331_, lean_object* v_as_332_, size_t v_i_333_, size_t v_stop_334_, uint64_t v_b_335_){
_start:
{
uint64_t v___x_336_; 
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_332_, v_i_333_, v_stop_334_, v_b_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_337_, lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_stop_340_, lean_object* v_b_341_){
_start:
{
uint8_t v_pu_boxed_342_; size_t v_i_boxed_343_; size_t v_stop_boxed_344_; uint64_t v_b_boxed_345_; uint64_t v_res_346_; lean_object* v_r_347_; 
v_pu_boxed_342_ = lean_unbox(v_pu_337_);
v_i_boxed_343_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_340_);
lean_dec(v_stop_340_);
v_b_boxed_345_ = lean_unbox_uint64(v_b_341_);
lean_dec_ref(v_b_341_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_342_, v_as_338_, v_i_boxed_343_, v_stop_boxed_344_, v_b_boxed_345_);
lean_dec_ref(v_as_338_);
v_r_347_ = lean_box_uint64(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_348_, lean_object* v_c_349_){
_start:
{
uint64_t v___x_350_; 
v___x_350_ = l_Lean_Compiler_LCNF_hashCode(v_pu_348_, v_c_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_351_, lean_object* v_c_352_){
_start:
{
uint8_t v_pu_boxed_353_; uint64_t v_res_354_; lean_object* v_r_355_; 
v_pu_boxed_353_ = lean_unbox(v_pu_351_);
v_res_354_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_353_, v_c_352_);
lean_dec_ref(v_c_352_);
v_r_355_ = lean_box_uint64(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___f_358_; 
v___x_357_ = lean_box(v_pu_356_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_358_, 0, v___x_357_);
return v___f_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_359_){
_start:
{
uint8_t v_pu_boxed_360_; lean_object* v_res_361_; 
v_pu_boxed_360_ = lean_unbox(v_pu_359_);
v_res_361_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_360_);
return v_res_361_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v_code_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; 
v_code_364_ = lean_ctor_get(v_x_363_, 0);
v___x_365_ = 0ULL;
v___x_366_ = l_Lean_Compiler_LCNF_hashCode(v_pu_362_, v_code_364_);
v___x_367_ = lean_uint64_mix_hash(v___x_365_, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v_externAttrData_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; 
v_externAttrData_368_ = lean_ctor_get(v_x_363_, 0);
v___x_369_ = 1ULL;
v___x_370_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_368_);
v___x_371_ = lean_uint64_mix_hash(v___x_369_, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_372_, lean_object* v_x_373_){
_start:
{
uint8_t v_pu_47__boxed_374_; uint64_t v_res_375_; lean_object* v_r_376_; 
v_pu_47__boxed_374_ = lean_unbox(v_pu_372_);
v_res_375_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_374_, v_x_373_);
lean_dec_ref(v_x_373_);
v_r_376_ = lean_box_uint64(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(v_pu_377_);
v___x_379_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* v_pu_380_){
_start:
{
uint8_t v_pu_5__boxed_381_; lean_object* v_res_382_; 
v_pu_5__boxed_381_ = lean_unbox(v_pu_380_);
v_res_382_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_5__boxed_381_);
return v_res_382_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
return v_x_383_;
}
else
{
lean_object* v_head_385_; lean_object* v_tail_386_; uint64_t v___y_388_; 
v_head_385_ = lean_ctor_get(v_x_384_, 0);
v_tail_386_ = lean_ctor_get(v_x_384_, 1);
if (lean_obj_tag(v_head_385_) == 0)
{
uint64_t v___x_391_; 
v___x_391_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_388_ = v___x_391_;
goto v___jp_387_;
}
else
{
uint64_t v_hash_392_; 
v_hash_392_ = lean_ctor_get_uint64(v_head_385_, sizeof(void*)*2);
v___y_388_ = v_hash_392_;
goto v___jp_387_;
}
v___jp_387_:
{
uint64_t v___x_389_; 
v___x_389_ = lean_uint64_mix_hash(v_x_383_, v___y_388_);
v_x_383_ = v___x_389_;
v_x_384_ = v_tail_386_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint64_t v_x_205__boxed_395_; uint64_t v_res_396_; lean_object* v_r_397_; 
v_x_205__boxed_395_ = lean_unbox_uint64(v_x_393_);
lean_dec_ref(v_x_393_);
v_res_396_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_205__boxed_395_, v_x_394_);
lean_dec(v_x_394_);
v_r_397_ = lean_box_uint64(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_398_){
_start:
{
lean_object* v_name_399_; lean_object* v_levelParams_400_; lean_object* v_type_401_; lean_object* v_params_402_; uint8_t v_safe_403_; uint64_t v___y_405_; uint64_t v___y_406_; uint64_t v___x_412_; uint64_t v___y_414_; 
v_name_399_ = lean_ctor_get(v_x_398_, 0);
v_levelParams_400_ = lean_ctor_get(v_x_398_, 1);
v_type_401_ = lean_ctor_get(v_x_398_, 2);
v_params_402_ = lean_ctor_get(v_x_398_, 3);
v_safe_403_ = lean_ctor_get_uint8(v_x_398_, sizeof(void*)*4);
v___x_412_ = 0ULL;
if (lean_obj_tag(v_name_399_) == 0)
{
uint64_t v___x_431_; 
v___x_431_ = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
v___y_414_ = v___x_431_;
goto v___jp_413_;
}
else
{
uint64_t v_hash_432_; 
v_hash_432_ = lean_ctor_get_uint64(v_name_399_, sizeof(void*)*2);
v___y_414_ = v_hash_432_;
goto v___jp_413_;
}
v___jp_404_:
{
uint64_t v___x_407_; 
v___x_407_ = lean_uint64_mix_hash(v___y_405_, v___y_406_);
if (v_safe_403_ == 0)
{
uint64_t v___x_408_; uint64_t v___x_409_; 
v___x_408_ = 13ULL;
v___x_409_ = lean_uint64_mix_hash(v___x_407_, v___x_408_);
return v___x_409_;
}
else
{
uint64_t v___x_410_; uint64_t v___x_411_; 
v___x_410_ = 11ULL;
v___x_411_ = lean_uint64_mix_hash(v___x_407_, v___x_410_);
return v___x_411_;
}
}
v___jp_413_:
{
uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_415_ = lean_uint64_mix_hash(v___x_412_, v___y_414_);
v___x_416_ = 7ULL;
v___x_417_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_416_, v_levelParams_400_);
v___x_418_ = lean_uint64_mix_hash(v___x_415_, v___x_417_);
v___x_419_ = l_Lean_Expr_hash(v_type_401_);
v___x_420_ = lean_uint64_mix_hash(v___x_418_, v___x_419_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_array_get_size(v_params_402_);
v___x_423_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
v___y_405_ = v___x_420_;
v___y_406_ = v___x_416_;
goto v___jp_404_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_le(v___x_422_, v___x_422_);
if (v___x_424_ == 0)
{
if (v___x_423_ == 0)
{
v___y_405_ = v___x_420_;
v___y_406_ = v___x_416_;
goto v___jp_404_;
}
else
{
size_t v___x_425_; size_t v___x_426_; uint64_t v___x_427_; 
v___x_425_ = ((size_t)0ULL);
v___x_426_ = lean_usize_of_nat(v___x_422_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_402_, v___x_425_, v___x_426_, v___x_416_);
v___y_405_ = v___x_420_;
v___y_406_ = v___x_427_;
goto v___jp_404_;
}
}
else
{
size_t v___x_428_; size_t v___x_429_; uint64_t v___x_430_; 
v___x_428_ = ((size_t)0ULL);
v___x_429_ = lean_usize_of_nat(v___x_422_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_402_, v___x_428_, v___x_429_, v___x_416_);
v___y_405_ = v___x_420_;
v___y_406_ = v___x_430_;
goto v___jp_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_433_){
_start:
{
uint64_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_433_);
lean_dec_ref(v_x_433_);
v_r_435_ = lean_box_uint64(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; 
v___x_438_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_pu_298__boxed_441_; uint64_t v_res_442_; lean_object* v_r_443_; 
v_pu_298__boxed_441_ = lean_unbox(v_pu_439_);
v_res_442_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_298__boxed_441_, v_x_440_);
lean_dec_ref(v_x_440_);
v_r_443_ = lean_box_uint64(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_box(v_pu_444_);
v___x_446_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* v_pu_447_){
_start:
{
uint8_t v_pu_5__boxed_448_; lean_object* v_res_449_; 
v_pu_5__boxed_448_ = lean_unbox(v_pu_447_);
v_res_449_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_5__boxed_448_);
return v_res_449_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_toSignature_452_; lean_object* v_value_453_; uint8_t v_recursive_454_; lean_object* v_inlineAttr_x3f_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___y_462_; 
v_toSignature_452_ = lean_ctor_get(v_x_451_, 0);
v_value_453_ = lean_ctor_get(v_x_451_, 1);
v_recursive_454_ = lean_ctor_get_uint8(v_x_451_, sizeof(void*)*3);
v_inlineAttr_x3f_455_ = lean_ctor_get(v_x_451_, 2);
v___x_456_ = 0ULL;
v___x_457_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_toSignature_452_);
v___x_458_ = lean_uint64_mix_hash(v___x_456_, v___x_457_);
v___x_459_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_450_, v_value_453_);
v___x_460_ = lean_uint64_mix_hash(v___x_458_, v___x_459_);
if (v_recursive_454_ == 0)
{
uint64_t v___x_472_; 
v___x_472_ = 13ULL;
v___y_462_ = v___x_472_;
goto v___jp_461_;
}
else
{
uint64_t v___x_473_; 
v___x_473_ = 11ULL;
v___y_462_ = v___x_473_;
goto v___jp_461_;
}
v___jp_461_:
{
uint64_t v___x_463_; 
v___x_463_ = lean_uint64_mix_hash(v___x_460_, v___y_462_);
if (lean_obj_tag(v_inlineAttr_x3f_455_) == 0)
{
uint64_t v___x_464_; uint64_t v___x_465_; 
v___x_464_ = 11ULL;
v___x_465_ = lean_uint64_mix_hash(v___x_463_, v___x_464_);
return v___x_465_;
}
else
{
lean_object* v_val_466_; uint8_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; 
v_val_466_ = lean_ctor_get(v_inlineAttr_x3f_455_, 0);
v___x_467_ = lean_unbox(v_val_466_);
v___x_468_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v___x_467_);
v___x_469_ = 13ULL;
v___x_470_ = lean_uint64_mix_hash(v___x_468_, v___x_469_);
v___x_471_ = lean_uint64_mix_hash(v___x_463_, v___x_470_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_pu_91__boxed_476_; uint64_t v_res_477_; lean_object* v_r_478_; 
v_pu_91__boxed_476_ = lean_unbox(v_pu_474_);
v_res_477_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_91__boxed_476_, v_x_475_);
lean_dec_ref(v_x_475_);
v_r_478_ = lean_box_uint64(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_box(v_pu_479_);
v___x_481_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* v_pu_482_){
_start:
{
uint8_t v_pu_5__boxed_483_; lean_object* v_res_484_; 
v_pu_5__boxed_483_ = lean_unbox(v_pu_482_);
v_res_484_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_5__boxed_483_);
return v_res_484_;
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
