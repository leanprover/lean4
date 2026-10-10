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
uint64_t l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(lean_object* v_p_1_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1_ = stack[0].m_obj;
uint64_t v_res_7_;
v_res_7_ = l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(v_p_1_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0___boxed(lean_object* v_p_8_){
_start:
{
uint64_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_Compiler_LCNF_instHashableParam___redArg___lam__0(v_p_8_);
lean_dec_ref(v_p_8_);
v_r_10_ = lean_box_uint64(v_res_9_);
return v_r_10_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg(){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0));
return v___f_13_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableParam___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l_Lean_Compiler_LCNF_instHashableParam___redArg();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Compiler_LCNF_instHashableParam___redArg();
return v_res_16_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t v_pu_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___redArg___closed__0));
return v___f_18_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_17_ = stack[0].m_num;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Compiler_LCNF_instHashableParam(v_pu_17_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object* v_pu_20_){
_start:
{
uint8_t v_pu_boxed_21_; lean_object* v_res_22_; 
v_pu_boxed_21_ = lean_unbox(v_pu_20_);
v_res_22_ = l_Lean_Compiler_LCNF_instHashableParam(v_pu_boxed_21_);
return v_res_22_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object* v_as_23_, size_t v_i_24_, size_t v_stop_25_, uint64_t v_b_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_usize_dec_eq(v_i_24_, v_stop_25_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v_fvarId_29_; lean_object* v_type_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; size_t v___x_35_; size_t v___x_36_; 
v___x_28_ = lean_array_uget_borrowed(v_as_23_, v_i_24_);
v_fvarId_29_ = lean_ctor_get(v___x_28_, 0);
v_type_30_ = lean_ctor_get(v___x_28_, 2);
v___x_31_ = l_Lean_instHashableFVarId_hash(v_fvarId_29_);
v___x_32_ = l_Lean_Expr_hash(v_type_30_);
v___x_33_ = lean_uint64_mix_hash(v___x_31_, v___x_32_);
v___x_34_ = lean_uint64_mix_hash(v_b_26_, v___x_33_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_add(v_i_24_, v___x_35_);
v_i_24_ = v___x_36_;
v_b_26_ = v___x_34_;
goto _start;
}
else
{
return v_b_26_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_23_ = stack[0].m_obj;
size_t v_i_24_ = stack[1].m_num;
size_t v_stop_25_ = stack[2].m_num;
uint64_t v_b_26_ = stack[3].m_num;
uint64_t v_res_38_;
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_as_23_, v_i_24_, v_stop_25_, v_b_26_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* v_as_39_, lean_object* v_i_40_, lean_object* v_stop_41_, lean_object* v_b_42_){
_start:
{
size_t v_i_boxed_43_; size_t v_stop_boxed_44_; uint64_t v_b_boxed_45_; uint64_t v_res_46_; lean_object* v_r_47_; 
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_stop_boxed_44_ = lean_unbox_usize(v_stop_41_);
lean_dec(v_stop_41_);
v_b_boxed_45_ = lean_unbox_uint64(v_b_42_);
lean_dec_ref(v_b_42_);
v_res_46_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_as_39_, v_i_boxed_43_, v_stop_boxed_44_, v_b_boxed_45_);
lean_dec_ref(v_as_39_);
v_r_47_ = lean_box_uint64(v_res_46_);
return v_r_47_;
}
}
uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object* v_ps_48_){
_start:
{
uint64_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_49_ = 7ULL;
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_array_get_size(v_ps_48_);
v___x_52_ = lean_nat_dec_lt(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
return v___x_49_;
}
else
{
size_t v___x_53_; size_t v___x_54_; uint64_t v___x_55_; 
v___x_53_ = ((size_t)0ULL);
v___x_54_ = lean_usize_of_nat(v___x_51_);
v___x_55_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_ps_48_, v___x_53_, v___x_54_, v___x_49_);
return v___x_55_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_hashParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_48_ = stack[0].m_obj;
uint64_t v_res_56_;
v_res_56_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_48_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object* v_ps_57_){
_start:
{
uint64_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_57_);
lean_dec_ref(v_ps_57_);
v_r_59_ = lean_box_uint64(v_res_58_);
return v_r_59_;
}
}
uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t v_pu_60_, lean_object* v_ps_61_){
_start:
{
uint64_t v___x_62_; 
v___x_62_ = l_Lean_Compiler_LCNF_hashParams___redArg(v_ps_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_hashParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_60_ = stack[0].m_num;
lean_object* v_ps_61_ = stack[1].m_obj;
uint64_t v_res_63_;
v_res_63_ = l_Lean_Compiler_LCNF_hashParams(v_pu_60_, v_ps_61_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* v_pu_64_, lean_object* v_ps_65_){
_start:
{
uint8_t v_pu_boxed_66_; uint64_t v_res_67_; lean_object* v_r_68_; 
v_pu_boxed_66_ = lean_unbox(v_pu_64_);
v_res_67_ = l_Lean_Compiler_LCNF_hashParams(v_pu_boxed_66_, v_ps_65_);
lean_dec_ref(v_ps_65_);
v_r_68_ = lean_box_uint64(v_res_67_);
return v_r_68_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object* v_as_69_, size_t v_i_70_, size_t v_stop_71_, uint64_t v_b_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_70_, v_stop_71_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; size_t v___x_77_; size_t v___x_78_; 
v___x_74_ = lean_array_uget_borrowed(v_as_69_, v_i_70_);
v___x_75_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v___x_74_);
v___x_76_ = lean_uint64_mix_hash(v_b_72_, v___x_75_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_add(v_i_70_, v___x_77_);
v_i_70_ = v___x_78_;
v_b_72_ = v___x_76_;
goto _start;
}
else
{
return v_b_72_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_69_ = stack[0].m_obj;
size_t v_i_70_ = stack[1].m_num;
size_t v_stop_71_ = stack[2].m_num;
uint64_t v_b_72_ = stack[3].m_num;
uint64_t v_res_80_;
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_69_, v_i_70_, v_stop_71_, v_b_72_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object* v_as_81_, lean_object* v_i_82_, lean_object* v_stop_83_, lean_object* v_b_84_){
_start:
{
size_t v_i_boxed_85_; size_t v_stop_boxed_86_; uint64_t v_b_boxed_87_; uint64_t v_res_88_; lean_object* v_r_89_; 
v_i_boxed_85_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_stop_boxed_86_ = lean_unbox_usize(v_stop_83_);
lean_dec(v_stop_83_);
v_b_boxed_87_ = lean_unbox_uint64(v_b_84_);
lean_dec_ref(v_b_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_81_, v_i_boxed_85_, v_stop_boxed_86_, v_b_boxed_87_);
lean_dec_ref(v_as_81_);
v_r_89_ = lean_box_uint64(v_res_88_);
return v_r_89_;
}
}
uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t v_pu_90_, lean_object* v_alts_91_){
_start:
{
uint64_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_92_ = 7ULL;
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_alts_91_);
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
return v___x_92_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = lean_nat_dec_le(v___x_94_, v___x_94_);
if (v___x_96_ == 0)
{
if (v___x_95_ == 0)
{
return v___x_92_;
}
else
{
size_t v___x_97_; size_t v___x_98_; uint64_t v___x_99_; 
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_94_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_90_, v_alts_91_, v___x_97_, v___x_98_, v___x_92_);
return v___x_99_;
}
}
else
{
size_t v___x_100_; size_t v___x_101_; uint64_t v___x_102_; 
v___x_100_ = ((size_t)0ULL);
v___x_101_ = lean_usize_of_nat(v___x_94_);
v___x_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_90_, v_alts_91_, v___x_100_, v___x_101_, v___x_92_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_hashAlts_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_90_ = stack[0].m_num;
lean_object* v_alts_91_ = stack[1].m_obj;
uint64_t v_res_103_;
v_res_103_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_90_, v_alts_91_);
stack->m_num = v_res_103_;
}
uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t v_pu_104_, lean_object* v_code_105_){
_start:
{
switch(lean_obj_tag(v_code_105_))
{
case 0:
{
lean_object* v_decl_106_; lean_object* v_k_107_; lean_object* v_fvarId_108_; lean_object* v_type_109_; lean_object* v_value_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; 
v_decl_106_ = lean_ctor_get(v_code_105_, 0);
v_k_107_ = lean_ctor_get(v_code_105_, 1);
v_fvarId_108_ = lean_ctor_get(v_decl_106_, 0);
v_type_109_ = lean_ctor_get(v_decl_106_, 2);
v_value_110_ = lean_ctor_get(v_decl_106_, 3);
v___x_111_ = l_Lean_instHashableFVarId_hash(v_fvarId_108_);
v___x_112_ = l_Lean_Expr_hash(v_type_109_);
v___x_113_ = lean_uint64_mix_hash(v___x_111_, v___x_112_);
v___x_114_ = l_Lean_Compiler_LCNF_instHashableLetValue_hash(v_pu_104_, v_value_110_);
v___x_115_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_107_);
v___x_116_ = lean_uint64_mix_hash(v___x_114_, v___x_115_);
v___x_117_ = lean_uint64_mix_hash(v___x_113_, v___x_116_);
return v___x_117_;
}
case 3:
{
lean_object* v_fvarId_118_; lean_object* v_args_119_; uint64_t v___x_120_; uint64_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_fvarId_118_ = lean_ctor_get(v_code_105_, 0);
v_args_119_ = lean_ctor_get(v_code_105_, 1);
v___x_120_ = l_Lean_instHashableFVarId_hash(v_fvarId_118_);
v___x_121_ = 7ULL;
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v_args_119_);
v___x_124_ = lean_nat_dec_lt(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
uint64_t v___x_125_; 
v___x_125_ = lean_uint64_mix_hash(v___x_120_, v___x_121_);
return v___x_125_;
}
else
{
size_t v___x_126_; size_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_123_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_args_119_, v___x_126_, v___x_127_, v___x_121_);
v___x_129_ = lean_uint64_mix_hash(v___x_120_, v___x_128_);
return v___x_129_;
}
}
case 4:
{
lean_object* v_cases_130_; lean_object* v_resultType_131_; lean_object* v_discr_132_; lean_object* v_alts_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; 
v_cases_130_ = lean_ctor_get(v_code_105_, 0);
v_resultType_131_ = lean_ctor_get(v_cases_130_, 1);
v_discr_132_ = lean_ctor_get(v_cases_130_, 2);
v_alts_133_ = lean_ctor_get(v_cases_130_, 3);
v___x_134_ = l_Lean_instHashableFVarId_hash(v_discr_132_);
v___x_135_ = l_Lean_Expr_hash(v_resultType_131_);
v___x_136_ = lean_uint64_mix_hash(v___x_134_, v___x_135_);
v___x_137_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_104_, v_alts_133_);
v___x_138_ = lean_uint64_mix_hash(v___x_136_, v___x_137_);
return v___x_138_;
}
case 5:
{
lean_object* v_fvarId_139_; uint64_t v___x_140_; 
v_fvarId_139_ = lean_ctor_get(v_code_105_, 0);
v___x_140_ = l_Lean_instHashableFVarId_hash(v_fvarId_139_);
return v___x_140_;
}
case 6:
{
lean_object* v_type_141_; uint64_t v___x_142_; 
v_type_141_ = lean_ctor_get(v_code_105_, 0);
v___x_142_ = l_Lean_Expr_hash(v_type_141_);
return v___x_142_;
}
case 7:
{
lean_object* v_fvarId_143_; lean_object* v_i_144_; lean_object* v_y_145_; lean_object* v_k_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; 
v_fvarId_143_ = lean_ctor_get(v_code_105_, 0);
v_i_144_ = lean_ctor_get(v_code_105_, 1);
v_y_145_ = lean_ctor_get(v_code_105_, 2);
v_k_146_ = lean_ctor_get(v_code_105_, 3);
v___x_147_ = l_Lean_instHashableFVarId_hash(v_fvarId_143_);
v___x_148_ = lean_uint64_of_nat(v_i_144_);
v___x_149_ = lean_uint64_mix_hash(v___x_147_, v___x_148_);
v___x_150_ = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(v_y_145_);
v___x_151_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_146_);
v___x_152_ = lean_uint64_mix_hash(v___x_150_, v___x_151_);
v___x_153_ = lean_uint64_mix_hash(v___x_149_, v___x_152_);
return v___x_153_;
}
case 8:
{
lean_object* v_fvarId_154_; lean_object* v_i_155_; lean_object* v_y_156_; lean_object* v_k_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; 
v_fvarId_154_ = lean_ctor_get(v_code_105_, 0);
v_i_155_ = lean_ctor_get(v_code_105_, 1);
v_y_156_ = lean_ctor_get(v_code_105_, 2);
v_k_157_ = lean_ctor_get(v_code_105_, 3);
v___x_158_ = l_Lean_instHashableFVarId_hash(v_fvarId_154_);
v___x_159_ = lean_uint64_of_nat(v_i_155_);
v___x_160_ = lean_uint64_mix_hash(v___x_158_, v___x_159_);
v___x_161_ = l_Lean_instHashableFVarId_hash(v_y_156_);
v___x_162_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_157_);
v___x_163_ = lean_uint64_mix_hash(v___x_161_, v___x_162_);
v___x_164_ = lean_uint64_mix_hash(v___x_160_, v___x_163_);
return v___x_164_;
}
case 9:
{
lean_object* v_fvarId_165_; lean_object* v_i_166_; lean_object* v_offset_167_; lean_object* v_y_168_; lean_object* v_ty_169_; lean_object* v_k_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; 
v_fvarId_165_ = lean_ctor_get(v_code_105_, 0);
v_i_166_ = lean_ctor_get(v_code_105_, 1);
v_offset_167_ = lean_ctor_get(v_code_105_, 2);
v_y_168_ = lean_ctor_get(v_code_105_, 3);
v_ty_169_ = lean_ctor_get(v_code_105_, 4);
v_k_170_ = lean_ctor_get(v_code_105_, 5);
v___x_171_ = l_Lean_instHashableFVarId_hash(v_fvarId_165_);
v___x_172_ = lean_uint64_of_nat(v_i_166_);
v___x_173_ = lean_uint64_mix_hash(v___x_171_, v___x_172_);
v___x_174_ = lean_uint64_of_nat(v_offset_167_);
v___x_175_ = l_Lean_instHashableFVarId_hash(v_y_168_);
v___x_176_ = lean_uint64_mix_hash(v___x_174_, v___x_175_);
v___x_177_ = l_Lean_Expr_hash(v_ty_169_);
v___x_178_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_170_);
v___x_179_ = lean_uint64_mix_hash(v___x_177_, v___x_178_);
v___x_180_ = lean_uint64_mix_hash(v___x_176_, v___x_179_);
v___x_181_ = lean_uint64_mix_hash(v___x_173_, v___x_180_);
return v___x_181_;
}
case 10:
{
lean_object* v_fvarId_182_; lean_object* v_cidx_183_; lean_object* v_k_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; 
v_fvarId_182_ = lean_ctor_get(v_code_105_, 0);
v_cidx_183_ = lean_ctor_get(v_code_105_, 1);
v_k_184_ = lean_ctor_get(v_code_105_, 2);
v___x_185_ = l_Lean_instHashableFVarId_hash(v_fvarId_182_);
v___x_186_ = lean_uint64_of_nat(v_cidx_183_);
v___x_187_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_184_);
v___x_188_ = lean_uint64_mix_hash(v___x_186_, v___x_187_);
v___x_189_ = lean_uint64_mix_hash(v___x_185_, v___x_188_);
return v___x_189_;
}
case 11:
{
lean_object* v_fvarId_190_; lean_object* v_n_191_; uint8_t v_check_192_; uint8_t v_persistent_193_; lean_object* v_k_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___y_199_; uint64_t v___y_200_; uint64_t v___y_206_; 
v_fvarId_190_ = lean_ctor_get(v_code_105_, 0);
v_n_191_ = lean_ctor_get(v_code_105_, 1);
v_check_192_ = lean_ctor_get_uint8(v_code_105_, sizeof(void*)*3);
v_persistent_193_ = lean_ctor_get_uint8(v_code_105_, sizeof(void*)*3 + 1);
v_k_194_ = lean_ctor_get(v_code_105_, 2);
v___x_195_ = l_Lean_instHashableFVarId_hash(v_fvarId_190_);
v___x_196_ = lean_uint64_of_nat(v_n_191_);
v___x_197_ = lean_uint64_mix_hash(v___x_195_, v___x_196_);
if (v_persistent_193_ == 0)
{
uint64_t v___x_209_; 
v___x_209_ = 13ULL;
v___y_206_ = v___x_209_;
goto v___jp_205_;
}
else
{
uint64_t v___x_210_; 
v___x_210_ = 11ULL;
v___y_206_ = v___x_210_;
goto v___jp_205_;
}
v___jp_198_:
{
uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; 
v___x_201_ = lean_uint64_mix_hash(v___y_199_, v___y_200_);
v___x_202_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_194_);
v___x_203_ = lean_uint64_mix_hash(v___x_201_, v___x_202_);
v___x_204_ = lean_uint64_mix_hash(v___x_197_, v___x_203_);
return v___x_204_;
}
v___jp_205_:
{
if (v_check_192_ == 0)
{
uint64_t v___x_207_; 
v___x_207_ = 13ULL;
v___y_199_ = v___y_206_;
v___y_200_ = v___x_207_;
goto v___jp_198_;
}
else
{
uint64_t v___x_208_; 
v___x_208_ = 11ULL;
v___y_199_ = v___y_206_;
v___y_200_ = v___x_208_;
goto v___jp_198_;
}
}
}
case 12:
{
lean_object* v_fvarId_211_; lean_object* v_n_212_; uint8_t v_check_213_; uint8_t v_persistent_214_; lean_object* v_objs_x3f_215_; lean_object* v_k_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___y_221_; uint64_t v___y_222_; uint64_t v___y_228_; uint64_t v___y_229_; uint64_t v___y_237_; 
v_fvarId_211_ = lean_ctor_get(v_code_105_, 0);
v_n_212_ = lean_ctor_get(v_code_105_, 1);
v_check_213_ = lean_ctor_get_uint8(v_code_105_, sizeof(void*)*4);
v_persistent_214_ = lean_ctor_get_uint8(v_code_105_, sizeof(void*)*4 + 1);
v_objs_x3f_215_ = lean_ctor_get(v_code_105_, 2);
v_k_216_ = lean_ctor_get(v_code_105_, 3);
v___x_217_ = l_Lean_instHashableFVarId_hash(v_fvarId_211_);
v___x_218_ = lean_uint64_of_nat(v_n_212_);
v___x_219_ = lean_uint64_mix_hash(v___x_217_, v___x_218_);
if (v_persistent_214_ == 0)
{
uint64_t v___x_240_; 
v___x_240_ = 13ULL;
v___y_237_ = v___x_240_;
goto v___jp_236_;
}
else
{
uint64_t v___x_241_; 
v___x_241_ = 11ULL;
v___y_237_ = v___x_241_;
goto v___jp_236_;
}
v___jp_220_:
{
uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; 
v___x_223_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_216_);
v___x_224_ = lean_uint64_mix_hash(v___y_222_, v___x_223_);
v___x_225_ = lean_uint64_mix_hash(v___y_221_, v___x_224_);
v___x_226_ = lean_uint64_mix_hash(v___x_219_, v___x_225_);
return v___x_226_;
}
v___jp_227_:
{
uint64_t v___x_230_; 
v___x_230_ = lean_uint64_mix_hash(v___y_228_, v___y_229_);
if (lean_obj_tag(v_objs_x3f_215_) == 0)
{
uint64_t v___x_231_; 
v___x_231_ = 11ULL;
v___y_221_ = v___x_230_;
v___y_222_ = v___x_231_;
goto v___jp_220_;
}
else
{
lean_object* v_val_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; 
v_val_232_ = lean_ctor_get(v_objs_x3f_215_, 0);
v___x_233_ = lean_uint64_of_nat(v_val_232_);
v___x_234_ = 13ULL;
v___x_235_ = lean_uint64_mix_hash(v___x_233_, v___x_234_);
v___y_221_ = v___x_230_;
v___y_222_ = v___x_235_;
goto v___jp_220_;
}
}
v___jp_236_:
{
if (v_check_213_ == 0)
{
uint64_t v___x_238_; 
v___x_238_ = 13ULL;
v___y_228_ = v___y_237_;
v___y_229_ = v___x_238_;
goto v___jp_227_;
}
else
{
uint64_t v___x_239_; 
v___x_239_ = 11ULL;
v___y_228_ = v___y_237_;
v___y_229_ = v___x_239_;
goto v___jp_227_;
}
}
}
case 13:
{
lean_object* v_fvarId_242_; lean_object* v_k_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; 
v_fvarId_242_ = lean_ctor_get(v_code_105_, 0);
v_k_243_ = lean_ctor_get(v_code_105_, 1);
v___x_244_ = l_Lean_instHashableFVarId_hash(v_fvarId_242_);
v___x_245_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_243_);
v___x_246_ = lean_uint64_mix_hash(v___x_244_, v___x_245_);
return v___x_246_;
}
default: 
{
lean_object* v_decl_247_; lean_object* v_k_248_; lean_object* v_fvarId_249_; lean_object* v_params_250_; lean_object* v_type_251_; lean_object* v_value_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_decl_247_ = lean_ctor_get(v_code_105_, 0);
v_k_248_ = lean_ctor_get(v_code_105_, 1);
v_fvarId_249_ = lean_ctor_get(v_decl_247_, 0);
v_params_250_ = lean_ctor_get(v_decl_247_, 2);
v_type_251_ = lean_ctor_get(v_decl_247_, 3);
v_value_252_ = lean_ctor_get(v_decl_247_, 4);
v___x_253_ = l_Lean_instHashableFVarId_hash(v_fvarId_249_);
v___x_254_ = l_Lean_Expr_hash(v_type_251_);
v___x_255_ = lean_uint64_mix_hash(v___x_253_, v___x_254_);
v___x_256_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_value_252_);
v___x_257_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_k_248_);
v___x_258_ = lean_uint64_mix_hash(v___x_256_, v___x_257_);
v___x_259_ = lean_uint64_mix_hash(v___x_255_, v___x_258_);
v___x_260_ = 7ULL;
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_array_get_size(v_params_250_);
v___x_263_ = lean_nat_dec_lt(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
uint64_t v___x_264_; 
v___x_264_ = lean_uint64_mix_hash(v___x_259_, v___x_260_);
return v___x_264_;
}
else
{
size_t v___x_265_; size_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_262_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_250_, v___x_265_, v___x_266_, v___x_260_);
v___x_268_ = lean_uint64_mix_hash(v___x_259_, v___x_267_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_hashCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_104_ = stack[0].m_num;
lean_object* v_code_105_ = stack[1].m_obj;
uint64_t v_res_269_;
v_res_269_ = l_Lean_Compiler_LCNF_hashCode(v_pu_104_, v_code_105_);
stack->m_num = v_res_269_;
}
uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t v_pu_270_, lean_object* v_alt_271_){
_start:
{
switch(lean_obj_tag(v_alt_271_))
{
case 0:
{
lean_object* v_ctorName_272_; lean_object* v_params_273_; lean_object* v_code_274_; uint64_t v___y_276_; uint64_t v___y_277_; uint64_t v___y_282_; 
v_ctorName_272_ = lean_ctor_get(v_alt_271_, 0);
v_params_273_ = lean_ctor_get(v_alt_271_, 1);
v_code_274_ = lean_ctor_get(v_alt_271_, 2);
if (lean_obj_tag(v_ctorName_272_) == 0)
{
uint64_t v___x_290_; 
v___x_290_ = 1723ULL;
v___y_282_ = v___x_290_;
goto v___jp_281_;
}
else
{
uint64_t v_hash_291_; 
v_hash_291_ = lean_ctor_get_uint64(v_ctorName_272_, sizeof(void*)*2);
v___y_282_ = v_hash_291_;
goto v___jp_281_;
}
v___jp_275_:
{
uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; 
v___x_278_ = lean_uint64_mix_hash(v___y_276_, v___y_277_);
v___x_279_ = l_Lean_Compiler_LCNF_hashCode(v_pu_270_, v_code_274_);
v___x_280_ = lean_uint64_mix_hash(v___x_278_, v___x_279_);
return v___x_280_;
}
v___jp_281_:
{
uint64_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = 7ULL;
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_array_get_size(v_params_273_);
v___x_286_ = lean_nat_dec_lt(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
v___y_276_ = v___y_282_;
v___y_277_ = v___x_283_;
goto v___jp_275_;
}
else
{
size_t v___x_287_; size_t v___x_288_; uint64_t v___x_289_; 
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_285_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_273_, v___x_287_, v___x_288_, v___x_283_);
v___y_276_ = v___y_282_;
v___y_277_ = v___x_289_;
goto v___jp_275_;
}
}
}
case 1:
{
lean_object* v_info_292_; lean_object* v_code_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; 
v_info_292_ = lean_ctor_get(v_alt_271_, 0);
v_code_293_ = lean_ctor_get(v_alt_271_, 1);
v___x_294_ = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(v_info_292_);
v___x_295_ = l_Lean_Compiler_LCNF_hashCode(v_pu_270_, v_code_293_);
v___x_296_ = lean_uint64_mix_hash(v___x_294_, v___x_295_);
return v___x_296_;
}
default: 
{
lean_object* v_code_297_; uint64_t v___x_298_; 
v_code_297_ = lean_ctor_get(v_alt_271_, 0);
v___x_298_ = l_Lean_Compiler_LCNF_hashCode(v_pu_270_, v_code_297_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_hashAlt_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_270_ = stack[0].m_num;
lean_object* v_alt_271_ = stack[1].m_obj;
uint64_t v_res_299_;
v_res_299_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_270_, v_alt_271_);
stack->m_num = v_res_299_;
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t v_pu_300_, lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, uint64_t v_b_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_302_, v_stop_303_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; size_t v___x_309_; size_t v___x_310_; 
v___x_306_ = lean_array_uget_borrowed(v_as_301_, v_i_302_);
v___x_307_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_300_, v___x_306_);
v___x_308_ = lean_uint64_mix_hash(v_b_304_, v___x_307_);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_add(v_i_302_, v___x_309_);
v_i_302_ = v___x_310_;
v_b_304_ = v___x_308_;
goto _start;
}
else
{
return v_b_304_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_300_ = stack[0].m_num;
lean_object* v_as_301_ = stack[1].m_obj;
size_t v_i_302_ = stack[2].m_num;
size_t v_stop_303_ = stack[3].m_num;
uint64_t v_b_304_ = stack[4].m_num;
uint64_t v_res_312_;
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_300_, v_as_301_, v_i_302_, v_stop_303_, v_b_304_);
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* v_pu_313_, lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_, lean_object* v_b_317_){
_start:
{
uint8_t v_pu_boxed_318_; size_t v_i_boxed_319_; size_t v_stop_boxed_320_; uint64_t v_b_boxed_321_; uint64_t v_res_322_; lean_object* v_r_323_; 
v_pu_boxed_318_ = lean_unbox(v_pu_313_);
v_i_boxed_319_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_320_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_b_boxed_321_ = lean_unbox_uint64(v_b_317_);
lean_dec_ref(v_b_317_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(v_pu_boxed_318_, v_as_314_, v_i_boxed_319_, v_stop_boxed_320_, v_b_boxed_321_);
lean_dec_ref(v_as_314_);
v_r_323_ = lean_box_uint64(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* v_pu_324_, lean_object* v_alts_325_){
_start:
{
uint8_t v_pu_boxed_326_; uint64_t v_res_327_; lean_object* v_r_328_; 
v_pu_boxed_326_ = lean_unbox(v_pu_324_);
v_res_327_ = l_Lean_Compiler_LCNF_hashAlts(v_pu_boxed_326_, v_alts_325_);
lean_dec_ref(v_alts_325_);
v_r_328_ = lean_box_uint64(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* v_pu_329_, lean_object* v_alt_330_){
_start:
{
uint8_t v_pu_boxed_331_; uint64_t v_res_332_; lean_object* v_r_333_; 
v_pu_boxed_331_ = lean_unbox(v_pu_329_);
v_res_332_ = l_Lean_Compiler_LCNF_hashAlt(v_pu_boxed_331_, v_alt_330_);
lean_dec_ref(v_alt_330_);
v_r_333_ = lean_box_uint64(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* v_pu_334_, lean_object* v_code_335_){
_start:
{
uint8_t v_pu_boxed_336_; uint64_t v_res_337_; lean_object* v_r_338_; 
v_pu_boxed_336_ = lean_unbox(v_pu_334_);
v_res_337_ = l_Lean_Compiler_LCNF_hashCode(v_pu_boxed_336_, v_code_335_);
lean_dec_ref(v_code_335_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t v_pu_339_, lean_object* v_as_340_, size_t v_i_341_, size_t v_stop_342_, uint64_t v_b_343_){
_start:
{
uint64_t v___x_344_; 
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(v_as_340_, v_i_341_, v_stop_342_, v_b_343_);
return v___x_344_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_339_ = stack[0].m_num;
lean_object* v_as_340_ = stack[1].m_obj;
size_t v_i_341_ = stack[2].m_num;
size_t v_stop_342_ = stack[3].m_num;
uint64_t v_b_343_ = stack[4].m_num;
uint64_t v_res_345_;
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_339_, v_as_340_, v_i_341_, v_stop_342_, v_b_343_);
stack->m_num = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* v_pu_346_, lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_, lean_object* v_b_350_){
_start:
{
uint8_t v_pu_boxed_351_; size_t v_i_boxed_352_; size_t v_stop_boxed_353_; uint64_t v_b_boxed_354_; uint64_t v_res_355_; lean_object* v_r_356_; 
v_pu_boxed_351_ = lean_unbox(v_pu_346_);
v_i_boxed_352_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_353_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_b_boxed_354_ = lean_unbox_uint64(v_b_350_);
lean_dec_ref(v_b_350_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(v_pu_boxed_351_, v_as_347_, v_i_boxed_352_, v_stop_boxed_353_, v_b_boxed_354_);
lean_dec_ref(v_as_347_);
v_r_356_ = lean_box_uint64(v_res_355_);
return v_r_356_;
}
}
uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t v_pu_357_, lean_object* v_c_358_){
_start:
{
uint64_t v___x_359_; 
v___x_359_ = l_Lean_Compiler_LCNF_hashCode(v_pu_357_, v_c_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableCode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_357_ = stack[0].m_num;
lean_object* v_c_358_ = stack[1].m_obj;
uint64_t v_res_360_;
v_res_360_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_357_, v_c_358_);
stack->m_num = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* v_pu_361_, lean_object* v_c_362_){
_start:
{
uint8_t v_pu_boxed_363_; uint64_t v_res_364_; lean_object* v_r_365_; 
v_pu_boxed_363_ = lean_unbox(v_pu_361_);
v_res_364_ = l_Lean_Compiler_LCNF_instHashableCode___lam__0(v_pu_boxed_363_, v_c_362_);
lean_dec_ref(v_c_362_);
v_r_365_ = lean_box_uint64(v_res_364_);
return v_r_365_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t v_pu_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___f_368_; 
v___x_367_ = lean_box(v_pu_366_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(v___f_368_, 0, v___x_367_);
return v___f_368_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_366_ = stack[0].m_num;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_366_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* v_pu_370_){
_start:
{
uint8_t v_pu_boxed_371_; lean_object* v_res_372_; 
v_pu_boxed_371_ = lean_unbox(v_pu_370_);
v_res_372_ = l_Lean_Compiler_LCNF_instHashableCode(v_pu_boxed_371_);
return v_res_372_;
}
}
uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t v_pu_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v_code_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; 
v_code_375_ = lean_ctor_get(v_x_374_, 0);
v___x_376_ = 0ULL;
v___x_377_ = l_Lean_Compiler_LCNF_hashCode(v_pu_373_, v_code_375_);
v___x_378_ = lean_uint64_mix_hash(v___x_376_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v_externAttrData_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; 
v_externAttrData_379_ = lean_ctor_get(v_x_374_, 0);
v___x_380_ = 1ULL;
v___x_381_ = l_Lean_instHashableExternAttrData_hash(v_externAttrData_379_);
v___x_382_ = lean_uint64_mix_hash(v___x_380_, v___x_381_);
return v___x_382_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableDeclValue_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_373_ = stack[0].m_num;
lean_object* v_x_374_ = stack[1].m_obj;
uint64_t v_res_383_;
v_res_383_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_373_, v_x_374_);
stack->m_num = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* v_pu_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_pu_47__boxed_386_; uint64_t v_res_387_; lean_object* v_r_388_; 
v_pu_47__boxed_386_ = lean_unbox(v_pu_384_);
v_res_387_ = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(v_pu_47__boxed_386_, v_x_385_);
lean_dec_ref(v_x_385_);
v_r_388_ = lean_box_uint64(v_res_387_);
return v_r_388_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t v_pu_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(v_pu_389_);
v___x_391_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableDeclValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_389_ = stack[0].m_num;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Compiler_LCNF_instHashableDeclValue(v_pu_389_);
stack->m_obj
 = v_res_392_;
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
uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t v_x_396_, lean_object* v_x_397_){
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
LEAN_EXPORT void l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_396_ = stack[0].m_num;
lean_object* v_x_397_ = stack[1].m_obj;
uint64_t v_res_406_;
v_res_406_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_396_, v_x_397_);
stack->m_num = v_res_406_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
uint64_t v_x_184__boxed_409_; uint64_t v_res_410_; lean_object* v_r_411_; 
v_x_184__boxed_409_ = lean_unbox_uint64(v_x_407_);
lean_dec_ref(v_x_407_);
v_res_410_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v_x_184__boxed_409_, v_x_408_);
lean_dec(v_x_408_);
v_r_411_ = lean_box_uint64(v_res_410_);
return v_r_411_;
}
}
uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* v_x_412_){
_start:
{
lean_object* v_name_413_; lean_object* v_levelParams_414_; lean_object* v_type_415_; lean_object* v_params_416_; uint8_t v_safe_417_; uint64_t v___y_419_; uint64_t v___y_420_; uint64_t v___x_426_; uint64_t v___y_428_; 
v_name_413_ = lean_ctor_get(v_x_412_, 0);
v_levelParams_414_ = lean_ctor_get(v_x_412_, 1);
v_type_415_ = lean_ctor_get(v_x_412_, 2);
v_params_416_ = lean_ctor_get(v_x_412_, 3);
v_safe_417_ = lean_ctor_get_uint8(v_x_412_, sizeof(void*)*4);
v___x_426_ = 0ULL;
if (lean_obj_tag(v_name_413_) == 0)
{
uint64_t v___x_441_; 
v___x_441_ = 1723ULL;
v___y_428_ = v___x_441_;
goto v___jp_427_;
}
else
{
uint64_t v_hash_442_; 
v_hash_442_ = lean_ctor_get_uint64(v_name_413_, sizeof(void*)*2);
v___y_428_ = v_hash_442_;
goto v___jp_427_;
}
v___jp_418_:
{
uint64_t v___x_421_; 
v___x_421_ = lean_uint64_mix_hash(v___y_419_, v___y_420_);
if (v_safe_417_ == 0)
{
uint64_t v___x_422_; uint64_t v___x_423_; 
v___x_422_ = 13ULL;
v___x_423_ = lean_uint64_mix_hash(v___x_421_, v___x_422_);
return v___x_423_;
}
else
{
uint64_t v___x_424_; uint64_t v___x_425_; 
v___x_424_ = 11ULL;
v___x_425_ = lean_uint64_mix_hash(v___x_421_, v___x_424_);
return v___x_425_;
}
}
v___jp_427_:
{
uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_429_ = lean_uint64_mix_hash(v___x_426_, v___y_428_);
v___x_430_ = 7ULL;
v___x_431_ = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(v___x_430_, v_levelParams_414_);
v___x_432_ = lean_uint64_mix_hash(v___x_429_, v___x_431_);
v___x_433_ = l_Lean_Expr_hash(v_type_415_);
v___x_434_ = lean_uint64_mix_hash(v___x_432_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_array_get_size(v_params_416_);
v___x_437_ = lean_nat_dec_lt(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
v___y_419_ = v___x_434_;
v___y_420_ = v___x_430_;
goto v___jp_418_;
}
else
{
size_t v___x_438_; size_t v___x_439_; uint64_t v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_436_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(v_params_416_, v___x_438_, v___x_439_, v___x_430_);
v___y_419_ = v___x_434_;
v___y_420_ = v___x_440_;
goto v___jp_418_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_412_ = stack[0].m_obj;
uint64_t v_res_443_;
v_res_443_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_412_);
stack->m_num = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* v_x_444_){
_start:
{
uint64_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_444_);
lean_dec_ref(v_x_444_);
v_r_446_ = lean_box_uint64(v_res_445_);
return v_r_446_;
}
}
uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t v_pu_447_, lean_object* v_x_448_){
_start:
{
uint64_t v___x_449_; 
v___x_449_ = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableSignature_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_447_ = stack[0].m_num;
lean_object* v_x_448_ = stack[1].m_obj;
uint64_t v_res_450_;
v_res_450_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_447_, v_x_448_);
stack->m_num = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* v_pu_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_pu_307__boxed_453_; uint64_t v_res_454_; lean_object* v_r_455_; 
v_pu_307__boxed_453_ = lean_unbox(v_pu_451_);
v_res_454_ = l_Lean_Compiler_LCNF_instHashableSignature_hash(v_pu_307__boxed_453_, v_x_452_);
lean_dec_ref(v_x_452_);
v_r_455_ = lean_box_uint64(v_res_454_);
return v_r_455_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t v_pu_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(v_pu_456_);
v___x_458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableSignature_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_456_ = stack[0].m_num;
lean_object* v_res_459_;
v_res_459_ = l_Lean_Compiler_LCNF_instHashableSignature(v_pu_456_);
stack->m_obj
 = v_res_459_;
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
uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t v_pu_463_, lean_object* v_x_464_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableDecl_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_463_ = stack[0].m_num;
lean_object* v_x_464_ = stack[1].m_obj;
uint64_t v_res_487_;
v_res_487_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_463_, v_x_464_);
stack->m_num = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* v_pu_488_, lean_object* v_x_489_){
_start:
{
uint8_t v_pu_92__boxed_490_; uint64_t v_res_491_; lean_object* v_r_492_; 
v_pu_92__boxed_490_ = lean_unbox(v_pu_488_);
v_res_491_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_92__boxed_490_, v_x_489_);
lean_dec_ref(v_x_489_);
v_r_492_ = lean_box_uint64(v_res_491_);
return v_r_492_;
}
}
lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t v_pu_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(v_pu_493_);
v___x_495_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instHashableDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_493_ = stack[0].m_num;
lean_object* v_res_496_;
v_res_496_ = l_Lean_Compiler_LCNF_instHashableDecl(v_pu_493_);
stack->m_obj
 = v_res_496_;
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
