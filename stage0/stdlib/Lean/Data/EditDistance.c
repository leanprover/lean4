// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: public import Init.Data.String.Basic import Init.Data.Vector.Basic import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Init.Data.Range import Init.While import Init.Data.String.Length
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_EditDistance_levenshtein___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_EditDistance_levenshtein___closed__0 = (const lean_object*)&l_Lean_EditDistance_levenshtein___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object* v_range_1_, lean_object* v_b_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_stop_4_; lean_object* v_step_5_; uint8_t v___x_6_; 
v_stop_4_ = lean_ctor_get(v_range_1_, 1);
v_step_5_ = lean_ctor_get(v_range_1_, 2);
v___x_6_ = lean_nat_dec_lt(v_i_3_, v_stop_4_);
if (v___x_6_ == 0)
{
lean_dec(v_i_3_);
return v_b_2_;
}
else
{
lean_object* v_v0_7_; lean_object* v___x_8_; 
lean_inc(v_i_3_);
v_v0_7_ = lean_array_fset(v_b_2_, v_i_3_, v_i_3_);
v___x_8_ = lean_nat_add(v_i_3_, v_step_5_);
lean_dec(v_i_3_);
v_b_2_ = v_v0_7_;
v_i_3_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object* v_range_10_, lean_object* v_b_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_10_, v_b_11_, v_i_12_);
lean_dec_ref(v_range_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(lean_object* v_str2_14_, lean_object* v___x_15_, lean_object* v___x_16_, lean_object* v___x_17_, lean_object* v_str1_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_snd_20_; lean_object* v_fst_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_70_; 
v_snd_20_ = lean_ctor_get(v_a_19_, 1);
v_fst_21_ = lean_ctor_get(v_a_19_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_a_19_);
if (v_isSharedCheck_70_ == 0)
{
v___x_23_ = v_a_19_;
v_isShared_24_ = v_isSharedCheck_70_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_snd_20_);
lean_inc(v_fst_21_);
lean_dec(v_a_19_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_70_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_69_; 
v_fst_25_ = lean_ctor_get(v_snd_20_, 0);
v_snd_26_ = lean_ctor_get(v_snd_20_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_snd_20_);
if (v_isSharedCheck_69_ == 0)
{
v___x_28_ = v_snd_20_;
v_isShared_29_ = v_isSharedCheck_69_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_snd_26_);
lean_inc(v_fst_25_);
lean_dec(v_snd_20_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_69_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; uint8_t v_decide_31_; 
v___x_30_ = lean_string_utf8_byte_size(v_str2_14_);
v_decide_31_ = lean_nat_dec_eq(v_fst_25_, v___x_30_);
if (v_decide_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___y_36_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___y_55_; uint32_t v___x_57_; uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_mod(v___x_32_, v___x_15_);
v___x_34_ = l_Fin_add(v___x_15_, v_snd_26_, v___x_33_);
lean_dec(v___x_33_);
v___x_50_ = lean_array_fget_borrowed(v___x_16_, v___x_34_);
v___x_51_ = lean_nat_add(v___x_50_, v___x_32_);
v___x_52_ = lean_array_fget_borrowed(v_fst_21_, v_snd_26_);
v___x_53_ = lean_nat_add(v___x_52_, v___x_32_);
v___x_57_ = lean_string_utf8_get_fast(v_str1_18_, v___x_17_);
v___x_58_ = lean_string_utf8_get_fast(v_str2_14_, v_fst_25_);
v___x_59_ = lean_uint32_dec_eq(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_array_fget_borrowed(v___x_16_, v_snd_26_);
lean_dec(v_snd_26_);
v___x_61_ = lean_nat_add(v___x_60_, v___x_32_);
v___y_55_ = v___x_61_;
goto v___jp_54_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_array_fget_borrowed(v___x_16_, v_snd_26_);
lean_dec(v_snd_26_);
lean_inc(v___x_62_);
v___y_55_ = v___x_62_;
goto v___jp_54_;
}
v___jp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_37_ = lean_array_fset(v_fst_21_, v___x_34_, v___y_36_);
v___x_38_ = lean_string_utf8_next_fast(v_str2_14_, v_fst_25_);
lean_dec(v_fst_25_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___x_34_);
lean_ctor_set(v___x_28_, 0, v___x_38_);
v___x_40_ = v___x_28_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_34_);
v___x_40_ = v_reuseFailAlloc_45_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_40_);
lean_ctor_set(v___x_23_, 0, v___x_37_);
v___x_42_ = v___x_23_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
v_a_19_ = v___x_42_;
goto _start;
}
}
}
v___jp_46_:
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_le(v___y_48_, v___y_47_);
if (v___x_49_ == 0)
{
lean_dec(v___y_48_);
v___y_36_ = v___y_47_;
goto v___jp_35_;
}
else
{
lean_dec(v___y_47_);
v___y_36_ = v___y_48_;
goto v___jp_35_;
}
}
v___jp_54_:
{
uint8_t v___x_56_; 
v___x_56_ = lean_nat_dec_le(v___x_51_, v___x_53_);
if (v___x_56_ == 0)
{
lean_dec(v___x_51_);
v___y_47_ = v___y_55_;
v___y_48_ = v___x_53_;
goto v___jp_46_;
}
else
{
lean_dec(v___x_53_);
v___y_47_ = v___y_55_;
v___y_48_ = v___x_51_;
goto v___jp_46_;
}
}
}
else
{
lean_object* v___x_64_; 
if (v_isShared_29_ == 0)
{
v___x_64_ = v___x_28_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_fst_25_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_snd_26_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_64_);
v___x_66_ = v___x_23_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_fst_21_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg___boxed(lean_object* v_str2_71_, lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_str1_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_71_, v___x_72_, v___x_73_, v___x_74_, v_str1_75_, v_a_76_);
lean_dec_ref(v_str1_75_);
lean_dec(v___x_74_);
lean_dec_ref(v___x_73_);
lean_dec(v___x_72_);
lean_dec_ref(v_str2_71_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object* v_cutoff_78_, lean_object* v_str1_79_, lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v_as_82_, size_t v_i_83_, size_t v_stop_84_){
_start:
{
uint8_t v___y_86_; uint8_t v___y_87_; uint8_t v___y_92_; lean_object* v___x_99_; uint8_t v_decide_100_; 
v___x_99_ = lean_string_utf8_byte_size(v_str1_79_);
v_decide_100_ = lean_nat_dec_eq(v___x_80_, v___x_99_);
if (v_decide_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = 1;
v___y_92_ = v___x_101_;
goto v___jp_91_;
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 0;
v___y_92_ = v___x_102_;
goto v___jp_91_;
}
v___jp_85_:
{
if (v___y_87_ == 0)
{
size_t v___x_88_; size_t v___x_89_; 
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_add(v_i_83_, v___x_88_);
v_i_83_ = v___x_89_;
goto _start;
}
else
{
return v___y_86_;
}
}
v___jp_91_:
{
uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_eq(v_i_83_, v_stop_84_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = 1;
v___x_95_ = lean_array_uget_borrowed(v_as_82_, v_i_83_);
v___x_96_ = lean_nat_dec_lt(v_cutoff_78_, v___x_95_);
if (v___x_96_ == 0)
{
v___y_86_ = v___x_94_;
v___y_87_ = v___y_92_;
goto v___jp_85_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_lt(v_cutoff_78_, v___x_81_);
v___y_86_ = v___x_94_;
v___y_87_ = v___x_97_;
goto v___jp_85_;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* v_cutoff_103_, lean_object* v_str1_104_, lean_object* v___x_105_, lean_object* v___x_106_, lean_object* v_as_107_, lean_object* v_i_108_, lean_object* v_stop_109_){
_start:
{
size_t v_i_boxed_110_; size_t v_stop_boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_i_boxed_110_ = lean_unbox_usize(v_i_108_);
lean_dec(v_i_108_);
v_stop_boxed_111_ = lean_unbox_usize(v_stop_109_);
lean_dec(v_stop_109_);
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_103_, v_str1_104_, v___x_105_, v___x_106_, v_as_107_, v_i_boxed_110_, v_stop_boxed_111_);
lean_dec_ref(v_as_107_);
lean_dec(v___x_106_);
lean_dec(v___x_105_);
lean_dec_ref(v_str1_104_);
lean_dec(v_cutoff_103_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object* v_str1_116_, lean_object* v___x_117_, lean_object* v_str2_118_, lean_object* v_cutoff_119_, lean_object* v___x_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_202_; 
v_snd_122_ = lean_ctor_get(v_a_121_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_121_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_a_121_, 0);
lean_dec(v_unused_203_);
v___x_124_ = v_a_121_;
v_isShared_125_ = v_isSharedCheck_202_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_dec(v_a_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_202_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_snd_126_; lean_object* v_snd_127_; lean_object* v_fst_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_200_; 
v_snd_126_ = lean_ctor_get(v_snd_122_, 1);
lean_inc(v_snd_126_);
v_snd_127_ = lean_ctor_get(v_snd_126_, 1);
lean_inc(v_snd_127_);
v_fst_128_ = lean_ctor_get(v_snd_122_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_snd_122_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_snd_122_, 1);
lean_dec(v_unused_201_);
v___x_130_ = v_snd_122_;
v_isShared_131_ = v_isSharedCheck_200_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_fst_128_);
lean_dec(v_snd_122_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_200_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_fst_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_198_; 
v_fst_132_ = lean_ctor_get(v_snd_126_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v_snd_126_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_snd_126_, 1);
lean_dec(v_unused_199_);
v___x_134_ = v_snd_126_;
v_isShared_135_ = v_isSharedCheck_198_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_fst_132_);
lean_dec(v_snd_126_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_198_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_197_; 
v_fst_136_ = lean_ctor_get(v_snd_127_, 0);
v_snd_137_ = lean_ctor_get(v_snd_127_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_snd_127_);
if (v_isSharedCheck_197_ == 0)
{
v___x_139_ = v_snd_127_;
v_isShared_140_ = v_isSharedCheck_197_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_inc(v_fst_136_);
lean_dec(v_snd_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_197_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v_decide_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = lean_string_utf8_byte_size(v_str1_116_);
v_decide_143_ = lean_nat_dec_eq(v_fst_136_, v___x_142_);
if (v_decide_143_ == 0)
{
lean_object* v___x_144_; lean_object* v_i_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v_i_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_nat_add(v_snd_137_, v___x_144_);
lean_dec(v_snd_137_);
lean_inc(v___x_146_);
v___x_147_ = lean_array_fset(v_fst_132_, v_i_145_, v___x_146_);
v___x_148_ = lean_nat_mod(v_i_145_, v___x_117_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_148_);
lean_ctor_set(v___x_139_, 0, v_i_145_);
v___x_150_ = v___x_139_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_i_145_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_184_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_150_);
lean_ctor_set(v___x_134_, 0, v___x_147_);
v___x_152_ = v___x_134_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_183_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v_fst_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_181_; 
v___x_153_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_118_, v___x_117_, v_fst_128_, v_fst_136_, v_str1_116_, v___x_152_);
v_fst_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v___x_153_, 1);
lean_dec(v_unused_182_);
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_181_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_fst_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_181_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_158_ = lean_string_utf8_next_fast(v_str1_116_, v_fst_136_);
v___x_171_ = lean_array_get_size(v_fst_154_);
v___x_172_ = lean_nat_dec_lt(v_i_145_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_fst_136_);
goto v___jp_159_;
}
else
{
if (v___x_172_ == 0)
{
lean_dec(v_fst_136_);
goto v___jp_159_;
}
else
{
size_t v___x_173_; size_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_171_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_119_, v_str1_116_, v_fst_136_, v___x_120_, v_fst_154_, v___x_173_, v___x_174_);
lean_dec(v_fst_136_);
if (v___x_175_ == 0)
{
goto v___jp_159_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_del_object(v___x_156_);
lean_del_object(v___x_130_);
lean_dec(v_fst_128_);
lean_del_object(v___x_124_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_158_);
lean_ctor_set(v___x_176_, 1, v___x_146_);
lean_inc(v_fst_154_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_fst_154_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_fst_154_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_141_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v_a_121_ = v___x_179_;
goto _start;
}
}
}
v___jp_159_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_146_);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_146_);
v___x_162_ = v_reuseFailAlloc_170_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_162_);
lean_ctor_set(v___x_130_, 0, v_fst_154_);
v___x_164_ = v___x_130_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_fst_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_169_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_164_);
lean_ctor_set(v___x_124_, 0, v_fst_128_);
v___x_166_ = v___x_124_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_fst_128_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_160_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_186_; 
if (v_isShared_140_ == 0)
{
v___x_186_ = v___x_139_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_fst_136_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_snd_137_);
v___x_186_ = v_reuseFailAlloc_196_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_186_);
v___x_188_ = v___x_134_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_195_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_188_);
v___x_190_ = v___x_130_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_fst_128_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_190_);
lean_ctor_set(v___x_124_, 0, v___x_141_);
v___x_192_ = v___x_124_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object* v_str1_204_, lean_object* v___x_205_, lean_object* v_str2_206_, lean_object* v_cutoff_207_, lean_object* v___x_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_204_, v___x_205_, v_str2_206_, v_cutoff_207_, v___x_208_, v_a_209_);
lean_dec(v___x_208_);
lean_dec(v_cutoff_207_);
lean_dec_ref(v_str2_206_);
lean_dec(v___x_205_);
lean_dec_ref(v_str1_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object* v_str2_211_, lean_object* v___x_212_, lean_object* v_str1_213_, lean_object* v_cutoff_214_, lean_object* v___x_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_snd_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_297_; 
v_snd_217_ = lean_ctor_get(v_a_216_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_a_216_, 0);
lean_dec(v_unused_298_);
v___x_219_ = v_a_216_;
v_isShared_220_ = v_isSharedCheck_297_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_snd_217_);
lean_dec(v_a_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_297_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_snd_221_; lean_object* v_snd_222_; lean_object* v_fst_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_295_; 
v_snd_221_ = lean_ctor_get(v_snd_217_, 1);
lean_inc(v_snd_221_);
v_snd_222_ = lean_ctor_get(v_snd_221_, 1);
lean_inc(v_snd_222_);
v_fst_223_ = lean_ctor_get(v_snd_217_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_snd_217_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_snd_217_, 1);
lean_dec(v_unused_296_);
v___x_225_ = v_snd_217_;
v_isShared_226_ = v_isSharedCheck_295_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_fst_223_);
lean_dec(v_snd_217_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_295_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_fst_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_293_; 
v_fst_227_ = lean_ctor_get(v_snd_221_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_snd_221_, 1);
lean_dec(v_unused_294_);
v___x_229_ = v_snd_221_;
v_isShared_230_ = v_isSharedCheck_293_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_fst_227_);
lean_dec(v_snd_221_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_293_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_292_; 
v_fst_231_ = lean_ctor_get(v_snd_222_, 0);
v_snd_232_ = lean_ctor_get(v_snd_222_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_snd_222_);
if (v_isSharedCheck_292_ == 0)
{
v___x_234_ = v_snd_222_;
v_isShared_235_ = v_isSharedCheck_292_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_snd_232_);
lean_inc(v_fst_231_);
lean_dec(v_snd_222_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_292_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v_decide_238_; 
v___x_236_ = lean_box(0);
v___x_237_ = lean_string_utf8_byte_size(v_str1_213_);
v_decide_238_ = lean_nat_dec_eq(v_fst_231_, v___x_237_);
if (v_decide_238_ == 0)
{
lean_object* v___x_239_; lean_object* v_i_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v_i_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_add(v_snd_232_, v___x_239_);
lean_dec(v_snd_232_);
lean_inc(v___x_241_);
v___x_242_ = lean_array_fset(v_fst_227_, v_i_240_, v___x_241_);
v___x_243_ = lean_nat_mod(v_i_240_, v___x_212_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_243_);
lean_ctor_set(v___x_234_, 0, v_i_240_);
v___x_245_ = v___x_234_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_i_240_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_279_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_245_);
lean_ctor_set(v___x_229_, 0, v___x_242_);
v___x_247_ = v___x_229_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_278_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v_fst_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_276_; 
v___x_248_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_211_, v___x_212_, v_fst_223_, v_fst_231_, v_str1_213_, v___x_247_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_248_, 1);
lean_dec(v_unused_277_);
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_276_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_fst_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_276_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_253_ = lean_string_utf8_next_fast(v_str1_213_, v_fst_231_);
v___x_266_ = lean_array_get_size(v_fst_249_);
v___x_267_ = lean_nat_dec_lt(v_i_240_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_fst_231_);
goto v___jp_254_;
}
else
{
if (v___x_267_ == 0)
{
lean_dec(v_fst_231_);
goto v___jp_254_;
}
else
{
size_t v___x_268_; size_t v___x_269_; uint8_t v___x_270_; 
v___x_268_ = ((size_t)0ULL);
v___x_269_ = lean_usize_of_nat(v___x_266_);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_214_, v_str1_213_, v_fst_231_, v___x_215_, v_fst_249_, v___x_268_, v___x_269_);
lean_dec(v_fst_231_);
if (v___x_270_ == 0)
{
goto v___jp_254_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_del_object(v___x_251_);
lean_del_object(v___x_225_);
lean_dec(v_fst_223_);
lean_del_object(v___x_219_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_253_);
lean_ctor_set(v___x_271_, 1, v___x_241_);
lean_inc(v_fst_249_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_fst_249_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_fst_249_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_236_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_213_, v___x_212_, v_str2_211_, v_cutoff_214_, v___x_215_, v___x_274_);
return v___x_275_;
}
}
}
v___jp_254_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_241_);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_241_);
v___x_257_ = v_reuseFailAlloc_265_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_257_);
lean_ctor_set(v___x_225_, 0, v_fst_249_);
v___x_259_ = v___x_225_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_fst_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_264_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_259_);
lean_ctor_set(v___x_219_, 0, v_fst_223_);
v___x_261_ = v___x_219_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fst_223_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_263_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_255_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_281_; 
if (v_isShared_235_ == 0)
{
v___x_281_ = v___x_234_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_snd_232_);
v___x_281_ = v_reuseFailAlloc_291_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_281_);
v___x_283_ = v___x_229_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_290_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_283_);
v___x_285_ = v___x_225_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_fst_223_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_285_);
lean_ctor_set(v___x_219_, 0, v___x_236_);
v___x_287_ = v___x_219_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object* v_str2_299_, lean_object* v___x_300_, lean_object* v_str1_301_, lean_object* v_cutoff_302_, lean_object* v___x_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_299_, v___x_300_, v_str1_301_, v_cutoff_302_, v___x_303_, v_a_304_);
lean_dec(v___x_303_);
lean_dec(v_cutoff_302_);
lean_dec_ref(v_str1_301_);
lean_dec(v___x_300_);
lean_dec_ref(v_str2_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* v_str1_308_, lean_object* v_str2_309_, lean_object* v_cutoff_310_){
_start:
{
lean_object* v_len1_311_; lean_object* v_len2_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_338_; uint8_t v___x_340_; 
v_len1_311_ = lean_string_length(v_str1_308_);
v_len2_312_ = lean_string_length(v_str2_309_);
v___x_340_ = lean_nat_dec_le(v_len1_311_, v_len2_312_);
if (v___x_340_ == 0)
{
v___y_338_ = v_len1_311_;
goto v___jp_337_;
}
else
{
v___y_338_ = v_len2_312_;
goto v___jp_337_;
}
v___jp_313_:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_nat_sub(v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec(v___y_314_);
v___x_317_ = lean_nat_dec_lt(v_cutoff_310_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_i_320_; lean_object* v_v1_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_fst_330_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_len2_312_, v___x_318_);
v_i_320_ = lean_unsigned_to_nat(0u);
lean_inc_n(v___x_319_, 2);
v_v1_321_ = lean_mk_array(v___x_319_, v_i_320_);
v___x_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_322_, 0, v_i_320_);
lean_ctor_set(v___x_322_, 1, v___x_319_);
lean_ctor_set(v___x_322_, 2, v___x_318_);
lean_inc_ref(v_v1_321_);
v___x_323_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_322_, v_v1_321_, v_i_320_);
lean_dec_ref_known(v___x_322_, 3);
v___x_324_ = lean_box(0);
v___x_325_ = ((lean_object*)(l_Lean_EditDistance_levenshtein___closed__0));
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_v1_321_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_309_, v___x_319_, v_str1_308_, v_cutoff_310_, v___x_316_, v___x_328_);
lean_dec(v___x_316_);
lean_dec(v___x_319_);
v_fst_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_fst_330_);
if (lean_obj_tag(v_fst_330_) == 0)
{
lean_object* v_snd_331_; lean_object* v_fst_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_snd_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v___x_329_);
v_fst_332_ = lean_ctor_get(v_snd_331_, 0);
lean_inc(v_fst_332_);
lean_dec(v_snd_331_);
v___x_333_ = lean_array_fget(v_fst_332_, v_len2_312_);
lean_dec(v_fst_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_val_335_; 
lean_dec_ref(v___x_329_);
v_val_335_ = lean_ctor_get(v_fst_330_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v_fst_330_, 1);
return v_val_335_;
}
}
else
{
lean_object* v___x_336_; 
lean_dec(v___x_316_);
v___x_336_ = lean_box(0);
return v___x_336_;
}
}
v___jp_337_:
{
uint8_t v___x_339_; 
v___x_339_ = lean_nat_dec_le(v_len1_311_, v_len2_312_);
if (v___x_339_ == 0)
{
v___y_314_ = v___y_338_;
v___y_315_ = v_len2_312_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___y_338_;
v___y_315_ = v_len1_311_;
goto v___jp_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* v_str1_341_, lean_object* v_str2_342_, lean_object* v_cutoff_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_EditDistance_levenshtein(v_str1_341_, v_str2_342_, v_cutoff_343_);
lean_dec(v_cutoff_343_);
lean_dec_ref(v_str2_342_);
lean_dec_ref(v_str1_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* v___x_345_, lean_object* v_range_346_, lean_object* v_b_347_, lean_object* v_i_348_, lean_object* v_hs_349_, lean_object* v_hl_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_346_, v_b_347_, v_i_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* v___x_352_, lean_object* v_range_353_, lean_object* v_b_354_, lean_object* v_i_355_, lean_object* v_hs_356_, lean_object* v_hl_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_352_, v_range_353_, v_b_354_, v_i_355_, v_hs_356_, v_hl_357_);
lean_dec_ref(v_range_353_);
lean_dec(v___x_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* v_str2_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v_str1_363_, lean_object* v_inst_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_359_, v___x_360_, v___x_361_, v___x_362_, v_str1_363_, v_a_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* v_str2_367_, lean_object* v___x_368_, lean_object* v___x_369_, lean_object* v___x_370_, lean_object* v_str1_371_, lean_object* v_inst_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_367_, v___x_368_, v___x_369_, v___x_370_, v_str1_371_, v_inst_372_, v_a_373_);
lean_dec_ref(v_str1_371_);
lean_dec(v___x_370_);
lean_dec_ref(v___x_369_);
lean_dec(v___x_368_);
lean_dec_ref(v_str2_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* v_str2_375_, lean_object* v___x_376_, lean_object* v_str1_377_, lean_object* v_cutoff_378_, lean_object* v___x_379_, lean_object* v_inst_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_375_, v___x_376_, v_str1_377_, v_cutoff_378_, v___x_379_, v_a_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* v_str2_383_, lean_object* v___x_384_, lean_object* v_str1_385_, lean_object* v_cutoff_386_, lean_object* v___x_387_, lean_object* v_inst_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_383_, v___x_384_, v_str1_385_, v_cutoff_386_, v___x_387_, v_inst_388_, v_a_389_);
lean_dec(v___x_387_);
lean_dec(v_cutoff_386_);
lean_dec_ref(v_str1_385_);
lean_dec(v___x_384_);
lean_dec_ref(v_str2_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* v_str1_391_, lean_object* v___x_392_, lean_object* v_str2_393_, lean_object* v_cutoff_394_, lean_object* v___x_395_, lean_object* v_inst_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_391_, v___x_392_, v_str2_393_, v_cutoff_394_, v___x_395_, v_a_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* v_str1_399_, lean_object* v___x_400_, lean_object* v_str2_401_, lean_object* v_cutoff_402_, lean_object* v___x_403_, lean_object* v_inst_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_399_, v___x_400_, v_str2_401_, v_cutoff_402_, v___x_403_, v_inst_404_, v_a_405_);
lean_dec(v___x_403_);
lean_dec(v_cutoff_402_);
lean_dec_ref(v_str2_401_);
lean_dec(v___x_400_);
lean_dec_ref(v_str1_399_);
return v_res_406_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_EditDistance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_EditDistance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_EditDistance(builtin);
}
#ifdef __cplusplus
}
#endif
