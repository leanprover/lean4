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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
size_t v___x_45_; size_t v___x_46_; uint64_t v___x_47_; 
v___x_45_ = ((size_t)0ULL);
v___x_46_ = lean_usize_of_nat(v___x_43_);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_40_, v___x_45_, v___x_46_, v___x_41_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object* v_ps_48_){
_start:
{
uint64_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_48_);
lean_dec_ref(v_ps_48_);
v_r_50_ = lean_box_uint64(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t v_pu_51_, lean_object* v_ps_52_){
_start:
{
uint64_t v___x_53_; 
v___x_53_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* v_pu_54_, lean_object* v_ps_55_){
_start:
{
uint8_t v_pu_boxed_56_; uint64_t v_res_57_; lean_object* v_r_58_; 
v_pu_boxed_56_ = lean_unbox(v_pu_54_);
v_res_57_ = l_Lean_Compiler_LCNF_hashParams(v_pu_boxed_56_, v_ps_55_);
lean_dec_ref(v_ps_55_);
v_r_58_ = lean_box_uint64(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object* v_as_59_, size_t v_i_60_, size_t v_stop_61_, uint64_t v_b_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_usize_dec_eq(v_i_60_, v_stop_61_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; size_t v___x_67_; size_t v___x_68_; 
v___x_64_ = lean_array_uget_borrowed(v_as_59_, v_i_60_);
v___x_65_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v___x_64_);
v___x_66_ = lean_uint64_mix_hash(v_b_62_, v___x_65_);
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_add(v_i_60_, v___x_67_);
v_i_60_ = v___x_68_;
v_b_62_ = v___x_66_;
goto _start;
}
else
{
return v_b_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_stop_72_, lean_object* v_b_73_){
_start:
{
size_t v_i_boxed_74_; size_t v_stop_boxed_75_; uint64_t v_b_boxed_76_; uint64_t v_res_77_; lean_object* v_r_78_; 
v_i_boxed_74_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_stop_boxed_75_ = lean_unbox_usize(v_stop_72_);
lean_dec(v_stop_72_);
v_b_boxed_76_ = lean_unbox_uint64(v_b_73_);
lean_dec_ref(v_b_73_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_70_, v_i_boxed_74_, v_stop_boxed_75_, v_b_boxed_76_);
lean_dec_ref(v_as_70_);
v_r_78_ = lean_box_uint64(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t v_pu_79_, lean_object* v_alts_80_){
_start:
{
uint64_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_81_ = 7ULL;
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_array_get_size(v_alts_80_);
v___x_84_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
return v___x_81_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_le(v___x_83_, v___x_83_);
if (v___x_85_ == 0)
{
if (v___x_84_ == 0)
{
return v___x_81_;
}
else
{
size_t v___x_86_; size_t v___x_87_; uint64_t v___x_88_; 
v___x_86_ = ((size_t)0ULL);
v___x_87_ = lean_usize_of_nat(v___x_83_);
v___x_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_79_, v_alts_80_, v___x_86_, v___x_87_, v___x_81_);
return v___x_88_;
}
}
else
{
size_t v___x_89_; size_t v___x_90_; uint64_t v___x_91_; 
v___x_89_ = ((size_t)0ULL);
v___x_90_ = lean_usize_of_nat(v___x_83_);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_79_, v_alts_80_, v___x_89_, v___x_90_, v___x_81_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t v_pu_92_, lean_object* v_code_93_){
_start:
{
switch(lean_obj_tag(v_code_93_))
{
case 0:
{
lean_object* v_decl_94_; lean_object* v_k_95_; lean_object* v_fvarId_96_; lean_object* v_type_97_; lean_object* v_value_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; 
v_decl_94_ = lean_ctor_get(v_code_93_, 0);
v_k_95_ = lean_ctor_get(v_code_93_, 1);
v_fvarId_96_ = lean_ctor_get(v_decl_94_, 0);
v_type_97_ = lean_ctor_get(v_decl_94_, 2);
v_value_98_ = lean_ctor_get(v_decl_94_, 3);
v___x_99_ = l_Lean_instHashableFVarId_hash(v_fvarId_96_);
v___x_100_ = l_Lean_Expr_hash(v_type_97_);
v___x_101_ = lean_uint64_mix_hash(v___x_99_, v___x_100_);
v___x_102_ = l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_92_, v_value_98_);
v___x_103_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_95_);
v___x_104_ = lean_uint64_mix_hash(v___x_102_, v___x_103_);
v___x_105_ = lean_uint64_mix_hash(v___x_101_, v___x_104_);
return v___x_105_;
}
case 3:
{
lean_object* v_fvarId_106_; lean_object* v_args_107_; uint64_t v___x_108_; uint64_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_fvarId_106_ = lean_ctor_get(v_code_93_, 0);
v_args_107_ = lean_ctor_get(v_code_93_, 1);
v___x_108_ = l_Lean_instHashableFVarId_hash(v_fvarId_106_);
v___x_109_ = 7ULL;
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_array_get_size(v_args_107_);
v___x_112_ = lean_nat_dec_lt(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
uint64_t v___x_113_; 
v___x_113_ = lean_uint64_mix_hash(v___x_108_, v___x_109_);
return v___x_113_;
}
else
{
size_t v___x_114_; size_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; 
v___x_114_ = ((size_t)0ULL);
v___x_115_ = lean_usize_of_nat(v___x_111_);
v___x_116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_107_, v___x_114_, v___x_115_, v___x_109_);
v___x_117_ = lean_uint64_mix_hash(v___x_108_, v___x_116_);
return v___x_117_;
}
}
case 4:
{
lean_object* v_cases_118_; lean_object* v_resultType_119_; lean_object* v_discr_120_; lean_object* v_alts_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; 
v_cases_118_ = lean_ctor_get(v_code_93_, 0);
v_resultType_119_ = lean_ctor_get(v_cases_118_, 1);
v_discr_120_ = lean_ctor_get(v_cases_118_, 2);
v_alts_121_ = lean_ctor_get(v_cases_118_, 3);
v___x_122_ = l_Lean_instHashableFVarId_hash(v_discr_120_);
v___x_123_ = l_Lean_Expr_hash(v_resultType_119_);
v___x_124_ = lean_uint64_mix_hash(v___x_122_, v___x_123_);
v___x_125_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_92_, v_alts_121_);
v___x_126_ = lean_uint64_mix_hash(v___x_124_, v___x_125_);
return v___x_126_;
}
case 5:
{
lean_object* v_fvarId_127_; uint64_t v___x_128_; 
v_fvarId_127_ = lean_ctor_get(v_code_93_, 0);
v___x_128_ = l_Lean_instHashableFVarId_hash(v_fvarId_127_);
return v___x_128_;
}
case 6:
{
lean_object* v_type_129_; uint64_t v___x_130_; 
v_type_129_ = lean_ctor_get(v_code_93_, 0);
v___x_130_ = l_Lean_Expr_hash(v_type_129_);
return v___x_130_;
}
case 7:
{
lean_object* v_fvarId_131_; lean_object* v_i_132_; lean_object* v_y_133_; lean_object* v_k_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; 
v_fvarId_131_ = lean_ctor_get(v_code_93_, 0);
v_i_132_ = lean_ctor_get(v_code_93_, 1);
v_y_133_ = lean_ctor_get(v_code_93_, 2);
v_k_134_ = lean_ctor_get(v_code_93_, 3);
v___x_135_ = l_Lean_instHashableFVarId_hash(v_fvarId_131_);
v___x_136_ = lean_uint64_of_nat(v_i_132_);
v___x_137_ = lean_uint64_mix_hash(v___x_135_, v___x_136_);
v___x_138_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_133_);
v___x_139_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_134_);
v___x_140_ = lean_uint64_mix_hash(v___x_138_, v___x_139_);
v___x_141_ = lean_uint64_mix_hash(v___x_137_, v___x_140_);
return v___x_141_;
}
case 8:
{
lean_object* v_fvarId_142_; lean_object* v_i_143_; lean_object* v_y_144_; lean_object* v_k_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; 
v_fvarId_142_ = lean_ctor_get(v_code_93_, 0);
v_i_143_ = lean_ctor_get(v_code_93_, 1);
v_y_144_ = lean_ctor_get(v_code_93_, 2);
v_k_145_ = lean_ctor_get(v_code_93_, 3);
v___x_146_ = l_Lean_instHashableFVarId_hash(v_fvarId_142_);
v___x_147_ = lean_uint64_of_nat(v_i_143_);
v___x_148_ = lean_uint64_mix_hash(v___x_146_, v___x_147_);
v___x_149_ = l_Lean_instHashableFVarId_hash(v_y_144_);
v___x_150_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_145_);
v___x_151_ = lean_uint64_mix_hash(v___x_149_, v___x_150_);
v___x_152_ = lean_uint64_mix_hash(v___x_148_, v___x_151_);
return v___x_152_;
}
case 9:
{
lean_object* v_fvarId_153_; lean_object* v_i_154_; lean_object* v_offset_155_; lean_object* v_y_156_; lean_object* v_ty_157_; lean_object* v_k_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; 
v_fvarId_153_ = lean_ctor_get(v_code_93_, 0);
v_i_154_ = lean_ctor_get(v_code_93_, 1);
v_offset_155_ = lean_ctor_get(v_code_93_, 2);
v_y_156_ = lean_ctor_get(v_code_93_, 3);
v_ty_157_ = lean_ctor_get(v_code_93_, 4);
v_k_158_ = lean_ctor_get(v_code_93_, 5);
v___x_159_ = l_Lean_instHashableFVarId_hash(v_fvarId_153_);
v___x_160_ = lean_uint64_of_nat(v_i_154_);
v___x_161_ = lean_uint64_mix_hash(v___x_159_, v___x_160_);
v___x_162_ = lean_uint64_of_nat(v_offset_155_);
v___x_163_ = l_Lean_instHashableFVarId_hash(v_y_156_);
v___x_164_ = lean_uint64_mix_hash(v___x_162_, v___x_163_);
v___x_165_ = l_Lean_Expr_hash(v_ty_157_);
v___x_166_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_158_);
v___x_167_ = lean_uint64_mix_hash(v___x_165_, v___x_166_);
v___x_168_ = lean_uint64_mix_hash(v___x_164_, v___x_167_);
v___x_169_ = lean_uint64_mix_hash(v___x_161_, v___x_168_);
return v___x_169_;
}
case 10:
{
lean_object* v_fvarId_170_; lean_object* v_cidx_171_; lean_object* v_k_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; 
v_fvarId_170_ = lean_ctor_get(v_code_93_, 0);
v_cidx_171_ = lean_ctor_get(v_code_93_, 1);
v_k_172_ = lean_ctor_get(v_code_93_, 2);
v___x_173_ = l_Lean_instHashableFVarId_hash(v_fvarId_170_);
v___x_174_ = lean_uint64_of_nat(v_cidx_171_);
v___x_175_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_172_);
v___x_176_ = lean_uint64_mix_hash(v___x_174_, v___x_175_);
v___x_177_ = lean_uint64_mix_hash(v___x_173_, v___x_176_);
return v___x_177_;
}
case 11:
{
lean_object* v_fvarId_178_; lean_object* v_n_179_; uint8_t v_check_180_; uint8_t v_persistent_181_; lean_object* v_k_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___y_187_; uint64_t v___y_188_; uint64_t v___y_194_; 
v_fvarId_178_ = lean_ctor_get(v_code_93_, 0);
v_n_179_ = lean_ctor_get(v_code_93_, 1);
v_check_180_ = lean_ctor_get_uint8(v_code_93_, sizeof(void*)*3);
v_persistent_181_ = lean_ctor_get_uint8(v_code_93_, sizeof(void*)*3 + 1);
v_k_182_ = lean_ctor_get(v_code_93_, 2);
v___x_183_ = l_Lean_instHashableFVarId_hash(v_fvarId_178_);
v___x_184_ = lean_uint64_of_nat(v_n_179_);
v___x_185_ = lean_uint64_mix_hash(v___x_183_, v___x_184_);
if (v_persistent_181_ == 0)
{
uint64_t v___x_197_; 
v___x_197_ = 13ULL;
v___y_194_ = v___x_197_;
goto v___jp_193_;
}
else
{
uint64_t v___x_198_; 
v___x_198_ = 11ULL;
v___y_194_ = v___x_198_;
goto v___jp_193_;
}
v___jp_186_:
{
uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; 
v___x_189_ = lean_uint64_mix_hash(v___y_187_, v___y_188_);
v___x_190_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_182_);
v___x_191_ = lean_uint64_mix_hash(v___x_189_, v___x_190_);
v___x_192_ = lean_uint64_mix_hash(v___x_185_, v___x_191_);
return v___x_192_;
}
v___jp_193_:
{
if (v_check_180_ == 0)
{
uint64_t v___x_195_; 
v___x_195_ = 13ULL;
v___y_187_ = v___y_194_;
v___y_188_ = v___x_195_;
goto v___jp_186_;
}
else
{
uint64_t v___x_196_; 
v___x_196_ = 11ULL;
v___y_187_ = v___y_194_;
v___y_188_ = v___x_196_;
goto v___jp_186_;
}
}
}
case 12:
{
lean_object* v_fvarId_199_; lean_object* v_n_200_; uint8_t v_check_201_; uint8_t v_persistent_202_; lean_object* v_objs_x3f_203_; lean_object* v_k_204_; uint64_t v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___y_209_; uint64_t v___y_210_; uint64_t v___y_216_; uint64_t v___y_217_; uint64_t v___y_225_; 
v_fvarId_199_ = lean_ctor_get(v_code_93_, 0);
v_n_200_ = lean_ctor_get(v_code_93_, 1);
v_check_201_ = lean_ctor_get_uint8(v_code_93_, sizeof(void*)*4);
v_persistent_202_ = lean_ctor_get_uint8(v_code_93_, sizeof(void*)*4 + 1);
v_objs_x3f_203_ = lean_ctor_get(v_code_93_, 2);
v_k_204_ = lean_ctor_get(v_code_93_, 3);
v___x_205_ = l_Lean_instHashableFVarId_hash(v_fvarId_199_);
v___x_206_ = lean_uint64_of_nat(v_n_200_);
v___x_207_ = lean_uint64_mix_hash(v___x_205_, v___x_206_);
if (v_persistent_202_ == 0)
{
uint64_t v___x_228_; 
v___x_228_ = 13ULL;
v___y_225_ = v___x_228_;
goto v___jp_224_;
}
else
{
uint64_t v___x_229_; 
v___x_229_ = 11ULL;
v___y_225_ = v___x_229_;
goto v___jp_224_;
}
v___jp_208_:
{
uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; 
v___x_211_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_204_);
v___x_212_ = lean_uint64_mix_hash(v___y_210_, v___x_211_);
v___x_213_ = lean_uint64_mix_hash(v___y_209_, v___x_212_);
v___x_214_ = lean_uint64_mix_hash(v___x_207_, v___x_213_);
return v___x_214_;
}
v___jp_215_:
{
uint64_t v___x_218_; 
v___x_218_ = lean_uint64_mix_hash(v___y_216_, v___y_217_);
if (lean_obj_tag(v_objs_x3f_203_) == 0)
{
uint64_t v___x_219_; 
v___x_219_ = 11ULL;
v___y_209_ = v___x_218_;
v___y_210_ = v___x_219_;
goto v___jp_208_;
}
else
{
lean_object* v_val_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; 
v_val_220_ = lean_ctor_get(v_objs_x3f_203_, 0);
v___x_221_ = lean_uint64_of_nat(v_val_220_);
v___x_222_ = 13ULL;
v___x_223_ = lean_uint64_mix_hash(v___x_221_, v___x_222_);
v___y_209_ = v___x_218_;
v___y_210_ = v___x_223_;
goto v___jp_208_;
}
}
v___jp_224_:
{
if (v_check_201_ == 0)
{
uint64_t v___x_226_; 
v___x_226_ = 13ULL;
v___y_216_ = v___y_225_;
v___y_217_ = v___x_226_;
goto v___jp_215_;
}
else
{
uint64_t v___x_227_; 
v___x_227_ = 11ULL;
v___y_216_ = v___y_225_;
v___y_217_ = v___x_227_;
goto v___jp_215_;
}
}
}
case 13:
{
lean_object* v_fvarId_230_; lean_object* v_k_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; 
v_fvarId_230_ = lean_ctor_get(v_code_93_, 0);
v_k_231_ = lean_ctor_get(v_code_93_, 1);
v___x_232_ = l_Lean_instHashableFVarId_hash(v_fvarId_230_);
v___x_233_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_231_);
v___x_234_ = lean_uint64_mix_hash(v___x_232_, v___x_233_);
return v___x_234_;
}
default: 
{
lean_object* v_decl_235_; lean_object* v_k_236_; lean_object* v_fvarId_237_; lean_object* v_params_238_; lean_object* v_type_239_; lean_object* v_value_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_decl_235_ = lean_ctor_get(v_code_93_, 0);
v_k_236_ = lean_ctor_get(v_code_93_, 1);
v_fvarId_237_ = lean_ctor_get(v_decl_235_, 0);
v_params_238_ = lean_ctor_get(v_decl_235_, 2);
v_type_239_ = lean_ctor_get(v_decl_235_, 3);
v_value_240_ = lean_ctor_get(v_decl_235_, 4);
v___x_241_ = l_Lean_instHashableFVarId_hash(v_fvarId_237_);
v___x_242_ = l_Lean_Expr_hash(v_type_239_);
v___x_243_ = lean_uint64_mix_hash(v___x_241_, v___x_242_);
v___x_244_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_value_240_);
v___x_245_ = l_Lean_Compiler_LCNF_hashCode(v_pu_92_, v_k_236_);
v___x_246_ = lean_uint64_mix_hash(v___x_244_, v___x_245_);
v___x_247_ = lean_uint64_mix_hash(v___x_243_, v___x_246_);
v___x_248_ = 7ULL;
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_array_get_size(v_params_238_);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
uint64_t v___x_252_; 
v___x_252_ = lean_uint64_mix_hash(v___x_247_, v___x_248_);
return v___x_252_;
}
else
{
size_t v___x_253_; size_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; 
v___x_253_ = ((size_t)0ULL);
v___x_254_ = lean_usize_of_nat(v___x_250_);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_238_, v___x_253_, v___x_254_, v___x_248_);
v___x_256_ = lean_uint64_mix_hash(v___x_247_, v___x_255_);
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_257_, lean_object* v_alt_258_){
_start:
{
switch(lean_obj_tag(v_alt_258_))
{
case 0:
{
lean_object* v_ctorName_259_; lean_object* v_params_260_; lean_object* v_code_261_; uint64_t v___y_263_; uint64_t v___y_264_; uint64_t v___y_269_; 
v_ctorName_259_ = lean_ctor_get(v_alt_258_, 0);
v_params_260_ = lean_ctor_get(v_alt_258_, 1);
v_code_261_ = lean_ctor_get(v_alt_258_, 2);
if (lean_obj_tag(v_ctorName_259_) == 0)
{
uint64_t v___x_277_; 
v___x_277_ = 1723ULL;
v___y_269_ = v___x_277_;
goto v___jp_268_;
}
else
{
uint64_t v_hash_278_; 
v_hash_278_ = lean_ctor_get_uint64(v_ctorName_259_, sizeof(void*)*2);
v___y_269_ = v_hash_278_;
goto v___jp_268_;
}
v___jp_262_:
{
uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; 
v___x_265_ = lean_uint64_mix_hash(v___y_263_, v___y_264_);
v___x_266_ = l_Lean_Compiler_LCNF_hashCode(v_pu_257_, v_code_261_);
v___x_267_ = lean_uint64_mix_hash(v___x_265_, v___x_266_);
return v___x_267_;
}
v___jp_268_:
{
uint64_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_270_ = 7ULL;
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_array_get_size(v_params_260_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
v___y_263_ = v___y_269_;
v___y_264_ = v___x_270_;
goto v___jp_262_;
}
else
{
size_t v___x_274_; size_t v___x_275_; uint64_t v___x_276_; 
v___x_274_ = ((size_t)0ULL);
v___x_275_ = lean_usize_of_nat(v___x_272_);
v___x_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_260_, v___x_274_, v___x_275_, v___x_270_);
v___y_263_ = v___y_269_;
v___y_264_ = v___x_276_;
goto v___jp_262_;
}
}
}
case 1:
{
lean_object* v_info_279_; lean_object* v_code_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; 
v_info_279_ = lean_ctor_get(v_alt_258_, 0);
v_code_280_ = lean_ctor_get(v_alt_258_, 1);
v___x_281_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_279_);
v___x_282_ = l_Lean_Compiler_LCNF_hashCode(v_pu_257_, v_code_280_);
v___x_283_ = lean_uint64_mix_hash(v___x_281_, v___x_282_);
return v___x_283_;
}
default: 
{
lean_object* v_code_284_; uint64_t v___x_285_; 
v_code_284_ = lean_ctor_get(v_alt_258_, 0);
v___x_285_ = l_Lean_Compiler_LCNF_hashCode(v_pu_257_, v_code_284_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_286_, lean_object* v_as_287_, size_t v_i_288_, size_t v_stop_289_, uint64_t v_b_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_eq(v_i_288_, v_stop_289_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; size_t v___x_295_; size_t v___x_296_; 
v___x_292_ = lean_array_uget_borrowed(v_as_287_, v_i_288_);
v___x_293_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_286_, v___x_292_);
v___x_294_ = lean_uint64_mix_hash(v_b_290_, v___x_293_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_288_, v___x_295_);
v_i_288_ = v___x_296_;
v_b_290_ = v___x_294_;
goto _start;
}
else
{
return v_b_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_298_, lean_object* v_as_299_, lean_object* v_i_300_, lean_object* v_stop_301_, lean_object* v_b_302_){
_start:
{
uint8_t v_pu_boxed_303_; size_t v_i_boxed_304_; size_t v_stop_boxed_305_; uint64_t v_b_boxed_306_; uint64_t v_res_307_; lean_object* v_r_308_; 
v_pu_boxed_303_ = lean_unbox(v_pu_298_);
v_i_boxed_304_ = lean_unbox_usize(v_i_300_);
lean_dec(v_i_300_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_301_);
lean_dec(v_stop_301_);
v_b_boxed_306_ = lean_unbox_uint64(v_b_302_);
lean_dec_ref(v_b_302_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_303_, v_as_299_, v_i_boxed_304_, v_stop_boxed_305_, v_b_boxed_306_);
lean_dec_ref(v_as_299_);
v_r_308_ = lean_box_uint64(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_309_, lean_object* v_alts_310_){
_start:
{
uint8_t v_pu_boxed_311_; uint64_t v_res_312_; lean_object* v_r_313_; 
v_pu_boxed_311_ = lean_unbox(v_pu_309_);
v_res_312_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_311_, v_alts_310_);
lean_dec_ref(v_alts_310_);
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
uint8_t v_pu_91__boxed_465_; uint64_t v_res_466_; lean_object* v_r_467_; 
v_pu_91__boxed_465_ = lean_unbox(v_pu_463_);
v_res_466_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_91__boxed_465_, v_x_464_);
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
