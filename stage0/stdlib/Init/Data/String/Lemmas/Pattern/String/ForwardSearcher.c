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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object* v_pat_1_, lean_object* v_stackPos_2_, lean_object* v_needlePos_3_, lean_object* v_s_4_, lean_object* v_n_5_, lean_object* v_h_6_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object* v_pat_12_, lean_object* v_stackPos_13_, lean_object* v_needlePos_14_, lean_object* v_s_15_, lean_object* v_n_16_, lean_object* v_h_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(v_pat_12_, v_stackPos_13_, v_needlePos_14_, v_s_15_, v_n_16_, v_h_17_);
lean_dec(v_n_16_);
lean_dec_ref(v_s_15_);
lean_dec(v_needlePos_14_);
lean_dec(v_stackPos_13_);
lean_dec_ref(v_pat_12_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object* v_pat_20_, lean_object* v_s_21_, lean_object* v_needlePos_22_, lean_object* v_stackPos_23_){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_byte_array_size(v_s_21_);
v___x_25_ = lean_nat_dec_le(v_stackPos_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_dec(v_stackPos_23_);
lean_dec(v_needlePos_22_);
lean_dec_ref(v_s_21_);
lean_dec_ref(v_pat_20_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_byte_array_size(v_pat_20_);
v___x_27_ = lean_nat_dec_le(v_needlePos_22_, v___x_26_);
if (v___x_27_ == 0)
{
lean_dec(v_stackPos_23_);
lean_dec(v_needlePos_22_);
lean_dec_ref(v_s_21_);
lean_dec_ref(v_pat_20_);
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_le(v_needlePos_22_, v_stackPos_23_);
if (v___x_28_ == 0)
{
lean_dec(v_stackPos_23_);
lean_dec(v_needlePos_22_);
lean_dec_ref(v_s_21_);
lean_dec_ref(v_pat_20_);
return v___x_28_;
}
else
{
lean_object* v___f_29_; uint8_t v___x_30_; 
lean_inc(v_needlePos_22_);
v___f_29_ = lean_alloc_closure((void*)(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed), 6, 4);
lean_closure_set(v___f_29_, 0, v_pat_20_);
lean_closure_set(v___f_29_, 1, v_stackPos_23_);
lean_closure_set(v___f_29_, 2, v_needlePos_22_);
lean_closure_set(v___f_29_, 3, v_s_21_);
v___x_30_ = l_Nat_decidableBallLTTR___redArg(v_needlePos_22_, v___f_29_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object* v_pat_31_, lean_object* v_s_32_, lean_object* v_needlePos_33_, lean_object* v_stackPos_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_31_, v_s_32_, v_needlePos_33_, v_stackPos_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(lean_object* v_pat_37_, lean_object* v___x_38_, lean_object* v_k_39_, lean_object* v_n_40_, lean_object* v_h_41_){
_start:
{
uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_42_ = lean_byte_array_fget(v_pat_37_, v_n_40_);
v___x_43_ = lean_nat_sub(v___x_38_, v_k_39_);
v___x_44_ = lean_nat_add(v___x_43_, v_n_40_);
lean_dec(v___x_43_);
v___x_45_ = lean_byte_array_fget(v_pat_37_, v___x_44_);
lean_dec(v___x_44_);
v___x_46_ = lean_uint8_dec_eq(v___x_42_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0___boxed(lean_object* v_pat_47_, lean_object* v___x_48_, lean_object* v_k_49_, lean_object* v_n_50_, lean_object* v_h_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0(v_pat_47_, v___x_48_, v_k_49_, v_n_50_, v_h_51_);
lean_dec(v_n_50_);
lean_dec(v_k_49_);
lean_dec(v___x_48_);
lean_dec_ref(v_pat_47_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object* v_pat_54_, lean_object* v_stackPos_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___y_59_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_stackPos_55_, v___x_57_);
v___x_63_ = lean_byte_array_size(v_pat_54_);
v___x_64_ = lean_nat_dec_le(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_dec(v___x_62_);
v___y_59_ = v___x_64_;
goto v___jp_58_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_le(v_k_56_, v___x_63_);
if (v___x_65_ == 0)
{
lean_dec(v___x_62_);
v___y_59_ = v___x_65_;
goto v___jp_58_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = lean_nat_dec_le(v_k_56_, v___x_62_);
if (v___x_66_ == 0)
{
lean_dec(v___x_62_);
v___y_59_ = v___x_66_;
goto v___jp_58_;
}
else
{
lean_object* v___f_67_; uint8_t v___x_68_; 
lean_inc_n(v_k_56_, 2);
lean_inc_ref(v_pat_54_);
v___f_67_ = lean_alloc_closure((void*)(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_67_, 0, v_pat_54_);
lean_closure_set(v___f_67_, 1, v___x_62_);
lean_closure_set(v___f_67_, 2, v_k_56_);
v___x_68_ = l_Nat_decidableBallLTTR___redArg(v_k_56_, v___f_67_);
v___y_59_ = v___x_68_;
goto v___jp_58_;
}
}
}
v___jp_58_:
{
if (v___y_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_nat_sub(v_k_56_, v___x_57_);
lean_dec(v_k_56_);
v_k_56_ = v___x_60_;
goto _start;
}
else
{
lean_dec_ref(v_pat_54_);
return v_k_56_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object* v_pat_69_, lean_object* v_stackPos_70_, lean_object* v_k_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_69_, v_stackPos_70_, v_k_71_);
lean_dec(v_stackPos_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object* v_pat_73_, lean_object* v_stackPos_74_, lean_object* v_hst_75_, lean_object* v_k_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_73_, v_stackPos_74_, v_k_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object* v_pat_78_, lean_object* v_stackPos_79_, lean_object* v_hst_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(v_pat_78_, v_stackPos_79_, v_hst_80_, v_k_81_);
lean_dec(v_stackPos_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object* v_pat_83_, lean_object* v_stackPos_84_){
_start:
{
lean_object* v___x_85_; 
lean_inc(v_stackPos_84_);
v___x_85_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_83_, v_stackPos_84_, v_stackPos_84_);
lean_dec(v_stackPos_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object* v_pat_86_, lean_object* v_stackPos_87_, lean_object* v_hst_88_){
_start:
{
lean_object* v___x_89_; 
lean_inc(v_stackPos_87_);
v___x_89_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_86_, v_stackPos_87_, v_stackPos_87_);
lean_dec(v_stackPos_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object* v_pat_90_, lean_object* v_stackPos_91_, lean_object* v_guess_92_){
_start:
{
uint8_t v___x_93_; uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_byte_array_fget(v_pat_90_, v_guess_92_);
v___x_94_ = lean_byte_array_fget(v_pat_90_, v_stackPos_91_);
v___x_95_ = lean_uint8_dec_eq(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_dec_eq(v_guess_92_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_sub(v_guess_92_, v___x_98_);
lean_dec(v_guess_92_);
lean_inc(v___x_99_);
lean_inc_ref(v_pat_90_);
v___x_100_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_90_, v___x_99_, v___x_99_);
lean_dec(v___x_99_);
v_guess_92_ = v___x_100_;
goto _start;
}
else
{
lean_dec(v_guess_92_);
lean_dec_ref(v_pat_90_);
return v___x_96_;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref(v_pat_90_);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_guess_92_, v___x_102_);
lean_dec(v_guess_92_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object* v_pat_104_, lean_object* v_stackPos_105_, lean_object* v_guess_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_104_, v_stackPos_105_, v_guess_106_);
lean_dec(v_stackPos_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object* v_pat_108_, lean_object* v_stackPos_109_, lean_object* v_hst_110_, lean_object* v_guess_111_, lean_object* v_hg_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_108_, v_stackPos_109_, v_guess_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object* v_pat_114_, lean_object* v_stackPos_115_, lean_object* v_hst_116_, lean_object* v_guess_117_, lean_object* v_hg_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(v_pat_114_, v_stackPos_115_, v_hst_116_, v_guess_117_, v_hg_118_);
lean_dec(v_stackPos_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object* v_needlePos_120_, lean_object* v_stackPos_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_nat_sub(v_stackPos_121_, v_needlePos_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object* v_needlePos_123_, lean_object* v_stackPos_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(v_needlePos_123_, v_stackPos_124_);
lean_dec(v_stackPos_124_);
lean_dec(v_needlePos_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object* v_pat_126_, lean_object* v_s_127_, lean_object* v_needlePos_128_, lean_object* v_stackPos_129_, lean_object* v_h_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_nat_sub(v_stackPos_129_, v_needlePos_128_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object* v_pat_132_, lean_object* v_s_133_, lean_object* v_needlePos_134_, lean_object* v_stackPos_135_, lean_object* v_h_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(v_pat_132_, v_s_133_, v_needlePos_134_, v_stackPos_135_, v_h_136_);
lean_dec(v_stackPos_135_);
lean_dec(v_needlePos_134_);
lean_dec_ref(v_s_133_);
lean_dec_ref(v_pat_132_);
return v_res_137_;
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
