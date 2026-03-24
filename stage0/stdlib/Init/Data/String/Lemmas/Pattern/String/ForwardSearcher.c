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
uint8_t l_Nat_decidableBallLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_30_ = l_Nat_decidableBallLT___redArg(v_needlePos_22_, v___f_29_);
lean_dec(v_needlePos_22_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(lean_object* v_pat_37_, lean_object* v_stackPos_38_, lean_object* v_k_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_add(v_stackPos_38_, v___x_40_);
lean_inc(v_k_39_);
lean_inc_ref_n(v_pat_37_, 2);
v___x_42_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_37_, v_pat_37_, v_k_39_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; 
v___x_43_ = lean_nat_sub(v_k_39_, v___x_40_);
lean_dec(v_k_39_);
v_k_39_ = v___x_43_;
goto _start;
}
else
{
lean_dec_ref(v_pat_37_);
return v_k_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(lean_object* v_pat_45_, lean_object* v_stackPos_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_45_, v_stackPos_46_, v_k_47_);
lean_dec(v_stackPos_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(lean_object* v_pat_49_, lean_object* v_stackPos_50_, lean_object* v_hst_51_, lean_object* v_k_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_49_, v_stackPos_50_, v_k_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(lean_object* v_pat_54_, lean_object* v_stackPos_55_, lean_object* v_hst_56_, lean_object* v_k_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(v_pat_54_, v_stackPos_55_, v_hst_56_, v_k_57_);
lean_dec(v_stackPos_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(lean_object* v_pat_59_, lean_object* v_stackPos_60_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_stackPos_60_);
v___x_61_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_59_, v_stackPos_60_, v_stackPos_60_);
lean_dec(v_stackPos_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(lean_object* v_pat_62_, lean_object* v_stackPos_63_, lean_object* v_hst_64_){
_start:
{
lean_object* v___x_65_; 
lean_inc(v_stackPos_63_);
v___x_65_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_62_, v_stackPos_63_, v_stackPos_63_);
lean_dec(v_stackPos_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(lean_object* v_pat_66_, lean_object* v_stackPos_67_, lean_object* v_guess_68_){
_start:
{
uint8_t v___x_69_; uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = lean_byte_array_fget(v_pat_66_, v_guess_68_);
v___x_70_ = lean_byte_array_fget(v_pat_66_, v_stackPos_67_);
v___x_71_ = lean_uint8_dec_eq(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_nat_dec_eq(v_guess_68_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_sub(v_guess_68_, v___x_74_);
lean_dec(v_guess_68_);
lean_inc(v___x_75_);
lean_inc_ref(v_pat_66_);
v___x_76_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_66_, v___x_75_, v___x_75_);
lean_dec(v___x_75_);
v_guess_68_ = v___x_76_;
goto _start;
}
else
{
lean_dec(v_guess_68_);
lean_dec_ref(v_pat_66_);
return v___x_72_;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v_pat_66_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_guess_68_, v___x_78_);
lean_dec(v_guess_68_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(lean_object* v_pat_80_, lean_object* v_stackPos_81_, lean_object* v_guess_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_80_, v_stackPos_81_, v_guess_82_);
lean_dec(v_stackPos_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(lean_object* v_pat_84_, lean_object* v_stackPos_85_, lean_object* v_hst_86_, lean_object* v_guess_87_, lean_object* v_hg_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_84_, v_stackPos_85_, v_guess_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(lean_object* v_pat_90_, lean_object* v_stackPos_91_, lean_object* v_hst_92_, lean_object* v_guess_93_, lean_object* v_hg_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(v_pat_90_, v_stackPos_91_, v_hst_92_, v_guess_93_, v_hg_94_);
lean_dec(v_stackPos_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(lean_object* v_needlePos_96_, lean_object* v_stackPos_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_nat_sub(v_stackPos_97_, v_needlePos_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(lean_object* v_needlePos_99_, lean_object* v_stackPos_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(v_needlePos_99_, v_stackPos_100_);
lean_dec(v_stackPos_100_);
lean_dec(v_needlePos_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(lean_object* v_pat_102_, lean_object* v_s_103_, lean_object* v_needlePos_104_, lean_object* v_stackPos_105_, lean_object* v_h_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_nat_sub(v_stackPos_105_, v_needlePos_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(lean_object* v_pat_108_, lean_object* v_s_109_, lean_object* v_needlePos_110_, lean_object* v_stackPos_111_, lean_object* v_h_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(v_pat_108_, v_s_109_, v_needlePos_110_, v_stackPos_111_, v_h_112_);
lean_dec(v_stackPos_111_);
lean_dec(v_needlePos_110_);
lean_dec_ref(v_s_109_);
lean_dec_ref(v_pat_108_);
return v_res_113_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
