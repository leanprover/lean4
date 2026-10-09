// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
// Imports: public import Init.Data.String.Lemmas.Pattern.String.Basic public import Init.Data.String.Pattern.String public import Init.Data.String.Slice public import Init.Data.String.Search import all Init.Data.String.Slice import all Init.Data.String.Search import all Init.Data.String.Pattern.String import Init.Data.String.Lemmas.IsEmpty import Init.Data.Vector.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.String.Lemmas.Basic import Init.Data.String.OrderInstances
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
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Nat_decidableBallLTTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object* v_pat_1_, lean_object* v_stackPos_2_, lean_object* v_needlePos_3_, lean_object* v_s_4_, lean_object* v_n_5_, lean_object* v_h_6_){
_start:
{
uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; uint8_t v___x_11_; 
v___x_7_ = lean_byte_array_fget(v_pat_1_, v_n_5_);
v___x_8_ = lean_nat_sub(v_stackPos_2_, v_needlePos_3_);
v___x_9_ = lean_nat_add(v___x_8_, v_n_5_);
lean_dec(v___x_8_);
v___x_10_ = lean_byte_array_fget(v_s_4_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_uint8_dec_eq(v___x_7_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_1_ = stack[0].m_obj;
lean_object* v_stackPos_2_ = stack[1].m_obj;
lean_object* v_needlePos_3_ = stack[2].m_obj;
lean_object* v_s_4_ = stack[3].m_obj;
lean_object* v_n_5_ = stack[4].m_obj;
uint8_t v_res_12_;
v_res_12_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(v_pat_1_, v_stackPos_2_, v_needlePos_3_, v_s_4_, v_n_5_, lean_box(0));
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object* v_pat_13_, lean_object* v_stackPos_14_, lean_object* v_needlePos_15_, lean_object* v_s_16_, lean_object* v_n_17_, lean_object* v_h_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(v_pat_13_, v_stackPos_14_, v_needlePos_15_, v_s_16_, v_n_17_, v_h_18_);
lean_dec(v_n_17_);
lean_dec_ref(v_s_16_);
lean_dec(v_needlePos_15_);
lean_dec(v_stackPos_14_);
lean_dec_ref(v_pat_13_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object* v_pat_21_, lean_object* v_s_22_, lean_object* v_needlePos_23_, lean_object* v_stackPos_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_byte_array_size(v_s_22_);
v___x_26_ = lean_nat_dec_le(v_stackPos_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_dec(v_stackPos_24_);
lean_dec(v_needlePos_23_);
lean_dec_ref(v_s_22_);
lean_dec_ref(v_pat_21_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_byte_array_size(v_pat_21_);
v___x_28_ = lean_nat_dec_le(v_needlePos_23_, v___x_27_);
if (v___x_28_ == 0)
{
lean_dec(v_stackPos_24_);
lean_dec(v_needlePos_23_);
lean_dec_ref(v_s_22_);
lean_dec_ref(v_pat_21_);
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_le(v_needlePos_23_, v_stackPos_24_);
if (v___x_29_ == 0)
{
lean_dec(v_stackPos_24_);
lean_dec(v_needlePos_23_);
lean_dec_ref(v_s_22_);
lean_dec_ref(v_pat_21_);
return v___x_29_;
}
else
{
lean_object* v___f_30_; uint8_t v___x_31_; 
lean_inc(v_needlePos_23_);
v___f_30_ = lean_alloc_closure((void*)(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed), 6, 4);
lean_closure_set(v___f_30_, 0, v_pat_21_);
lean_closure_set(v___f_30_, 1, v_stackPos_24_);
lean_closure_set(v___f_30_, 2, v_needlePos_23_);
lean_closure_set(v___f_30_, 3, v_s_22_);
v___x_31_ = l_Nat_decidableBallLTTR___redArg(v_needlePos_23_, v___f_30_);
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_21_ = stack[0].m_obj;
lean_object* v_s_22_ = stack[1].m_obj;
lean_object* v_needlePos_23_ = stack[2].m_obj;
lean_object* v_stackPos_24_ = stack[3].m_obj;
uint8_t v_res_32_;
v_res_32_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_21_, v_s_22_, v_needlePos_23_, v_stackPos_24_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object* v_pat_33_, lean_object* v_s_34_, lean_object* v_needlePos_35_, lean_object* v_stackPos_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_33_, v_s_34_, v_needlePos_35_, v_stackPos_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(lean_object* v_pat_39_, lean_object* v___x_40_, lean_object* v_k_41_, lean_object* v_n_42_, lean_object* v_h_43_){
_start:
{
uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; 
v___x_44_ = lean_byte_array_fget(v_pat_39_, v_n_42_);
v___x_45_ = lean_nat_sub(v___x_40_, v_k_41_);
v___x_46_ = lean_nat_add(v___x_45_, v_n_42_);
lean_dec(v___x_45_);
v___x_47_ = lean_byte_array_fget(v_pat_39_, v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = lean_uint8_dec_eq(v___x_44_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_39_ = stack[0].m_obj;
lean_object* v___x_40_ = stack[1].m_obj;
lean_object* v_k_41_ = stack[2].m_obj;
lean_object* v_n_42_ = stack[3].m_obj;
uint8_t v_res_49_;
v_res_49_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(v_pat_39_, v___x_40_, v_k_41_, v_n_42_, lean_box(0));
stack->m_num = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0___boxed(lean_object* v_pat_50_, lean_object* v___x_51_, lean_object* v_k_52_, lean_object* v_n_53_, lean_object* v_h_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(v_pat_50_, v___x_51_, v_k_52_, v_n_53_, v_h_54_);
lean_dec(v_n_53_);
lean_dec(v_k_52_);
lean_dec(v___x_51_);
lean_dec_ref(v_pat_50_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object* v_pat_57_, lean_object* v_stackPos_58_, lean_object* v_k_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___y_62_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_stackPos_58_, v___x_60_);
v___x_66_ = lean_byte_array_size(v_pat_57_);
v___x_67_ = lean_nat_dec_le(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec(v___x_65_);
v___y_62_ = v___x_67_;
goto v___jp_61_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = lean_nat_dec_le(v_k_59_, v___x_66_);
if (v___x_68_ == 0)
{
lean_dec(v___x_65_);
v___y_62_ = v___x_68_;
goto v___jp_61_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_le(v_k_59_, v___x_65_);
if (v___x_69_ == 0)
{
lean_dec(v___x_65_);
v___y_62_ = v___x_69_;
goto v___jp_61_;
}
else
{
lean_object* v___f_70_; uint8_t v___x_71_; 
lean_inc_n(v_k_59_, 2);
lean_inc_ref(v_pat_57_);
v___f_70_ = lean_alloc_closure((void*)(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_70_, 0, v_pat_57_);
lean_closure_set(v___f_70_, 1, v___x_65_);
lean_closure_set(v___f_70_, 2, v_k_59_);
v___x_71_ = l_Nat_decidableBallLTTR___redArg(v_k_59_, v___f_70_);
v___y_62_ = v___x_71_;
goto v___jp_61_;
}
}
}
v___jp_61_:
{
if (v___y_62_ == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_nat_sub(v_k_59_, v___x_60_);
lean_dec(v_k_59_);
v_k_59_ = v___x_63_;
goto _start;
}
else
{
lean_dec_ref(v_pat_57_);
return v_k_59_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object* v_pat_72_, lean_object* v_stackPos_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_72_, v_stackPos_73_, v_k_74_);
lean_dec(v_stackPos_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object* v_pat_76_, lean_object* v_stackPos_77_, lean_object* v_hst_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_76_, v_stackPos_77_, v_k_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object* v_pat_81_, lean_object* v_stackPos_82_, lean_object* v_hst_83_, lean_object* v_k_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(v_pat_81_, v_stackPos_82_, v_hst_83_, v_k_84_);
lean_dec(v_stackPos_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object* v_pat_86_, lean_object* v_stackPos_87_){
_start:
{
lean_object* v___x_88_; 
lean_inc(v_stackPos_87_);
v___x_88_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_86_, v_stackPos_87_, v_stackPos_87_);
lean_dec(v_stackPos_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object* v_pat_89_, lean_object* v_stackPos_90_, lean_object* v_hst_91_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v_stackPos_90_);
v___x_92_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_89_, v_stackPos_90_, v_stackPos_90_);
lean_dec(v_stackPos_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object* v_pat_93_, lean_object* v_stackPos_94_, lean_object* v_guess_95_){
_start:
{
uint8_t v___x_96_; uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = lean_byte_array_fget(v_pat_93_, v_guess_95_);
v___x_97_ = lean_byte_array_fget(v_pat_93_, v_stackPos_94_);
v___x_98_ = lean_uint8_dec_eq(v___x_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_nat_dec_eq(v_guess_95_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_sub(v_guess_95_, v___x_101_);
lean_dec(v_guess_95_);
lean_inc(v___x_102_);
lean_inc_ref(v_pat_93_);
v___x_103_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_93_, v___x_102_, v___x_102_);
lean_dec(v___x_102_);
v_guess_95_ = v___x_103_;
goto _start;
}
else
{
lean_dec(v_guess_95_);
lean_dec_ref(v_pat_93_);
return v___x_99_;
}
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec_ref(v_pat_93_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_guess_95_, v___x_105_);
lean_dec(v_guess_95_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object* v_pat_107_, lean_object* v_stackPos_108_, lean_object* v_guess_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_107_, v_stackPos_108_, v_guess_109_);
lean_dec(v_stackPos_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object* v_pat_111_, lean_object* v_stackPos_112_, lean_object* v_hst_113_, lean_object* v_guess_114_, lean_object* v_hg_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_111_, v_stackPos_112_, v_guess_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object* v_pat_117_, lean_object* v_stackPos_118_, lean_object* v_hst_119_, lean_object* v_guess_120_, lean_object* v_hg_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(v_pat_117_, v_stackPos_118_, v_hst_119_, v_guess_120_, v_hg_121_);
lean_dec(v_stackPos_118_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object* v_needlePos_123_, lean_object* v_stackPos_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_nat_sub(v_stackPos_124_, v_needlePos_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object* v_needlePos_126_, lean_object* v_stackPos_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(v_needlePos_126_, v_stackPos_127_);
lean_dec(v_stackPos_127_);
lean_dec(v_needlePos_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object* v_pat_129_, lean_object* v_s_130_, lean_object* v_needlePos_131_, lean_object* v_stackPos_132_, lean_object* v_h_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_nat_sub(v_stackPos_132_, v_needlePos_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object* v_pat_135_, lean_object* v_s_136_, lean_object* v_needlePos_137_, lean_object* v_stackPos_138_, lean_object* v_h_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(v_pat_135_, v_s_136_, v_needlePos_137_, v_stackPos_138_, v_h_139_);
lean_dec(v_stackPos_138_);
lean_dec(v_needlePos_137_);
lean_dec_ref(v_s_136_);
lean_dec_ref(v_pat_135_);
return v_res_140_;
}
}
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Lemmas_Pattern_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
}
#ifdef __cplusplus
}
#endif
