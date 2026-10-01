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
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object* v_str1_118_, lean_object* v___x_119_, lean_object* v_str2_120_, lean_object* v_cutoff_121_, lean_object* v___x_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_snd_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_203_; 
v_snd_124_ = lean_ctor_get(v_a_123_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_a_123_, 0);
lean_dec(v_unused_204_);
v___x_126_ = v_a_123_;
v_isShared_127_ = v_isSharedCheck_203_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_snd_124_);
lean_dec(v_a_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_203_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_snd_128_; lean_object* v_snd_129_; lean_object* v_fst_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_201_; 
v_snd_128_ = lean_ctor_get(v_snd_124_, 1);
lean_inc(v_snd_128_);
v_snd_129_ = lean_ctor_get(v_snd_128_, 1);
lean_inc(v_snd_129_);
v_fst_130_ = lean_ctor_get(v_snd_124_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_snd_124_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_snd_124_, 1);
lean_dec(v_unused_202_);
v___x_132_ = v_snd_124_;
v_isShared_133_ = v_isSharedCheck_201_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_fst_130_);
lean_dec(v_snd_124_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_201_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_fst_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_199_; 
v_fst_134_ = lean_ctor_get(v_snd_128_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_snd_128_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_snd_128_, 1);
lean_dec(v_unused_200_);
v___x_136_ = v_snd_128_;
v_isShared_137_ = v_isSharedCheck_199_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_fst_134_);
lean_dec(v_snd_128_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_199_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_198_; 
v_fst_138_ = lean_ctor_get(v_snd_129_, 0);
v_snd_139_ = lean_ctor_get(v_snd_129_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_snd_129_);
if (v_isSharedCheck_198_ == 0)
{
v___x_141_ = v_snd_129_;
v_isShared_142_ = v_isSharedCheck_198_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_snd_139_);
lean_inc(v_fst_138_);
lean_dec(v_snd_129_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_198_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v_decide_145_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_string_utf8_byte_size(v_str1_118_);
v_decide_145_ = lean_nat_dec_eq(v_fst_138_, v___x_144_);
if (v_decide_145_ == 0)
{
lean_object* v___x_146_; lean_object* v_i_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v_i_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_nat_add(v_snd_139_, v___x_146_);
lean_dec(v_snd_139_);
lean_inc(v___x_148_);
v___x_149_ = lean_array_fset(v_fst_134_, v_i_147_, v___x_148_);
v___x_150_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_150_);
lean_ctor_set(v___x_141_, 0, v___x_149_);
v___x_152_ = v___x_141_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_185_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v_fst_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_183_; 
v___x_153_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_120_, v___x_119_, v_fst_130_, v_fst_138_, v_str1_118_, v___x_152_);
v_fst_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_153_, 1);
lean_dec(v_unused_184_);
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_183_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_fst_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_183_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_158_ = lean_string_utf8_next_fast(v_str1_118_, v_fst_138_);
v___x_173_ = lean_array_get_size(v_fst_154_);
v___x_174_ = lean_nat_dec_lt(v_i_147_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v_fst_138_);
goto v___jp_159_;
}
else
{
if (v___x_174_ == 0)
{
lean_dec(v_fst_138_);
goto v___jp_159_;
}
else
{
size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = ((size_t)0ULL);
v___x_176_ = lean_usize_of_nat(v___x_173_);
v___x_177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_121_, v_str1_118_, v_fst_138_, v___x_122_, v_fst_154_, v___x_175_, v___x_176_);
lean_dec(v_fst_138_);
if (v___x_177_ == 0)
{
goto v___jp_159_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_del_object(v___x_156_);
lean_del_object(v___x_136_);
lean_del_object(v___x_132_);
lean_dec(v_fst_130_);
lean_del_object(v___x_126_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_158_);
lean_ctor_set(v___x_178_, 1, v___x_148_);
lean_inc(v_fst_154_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_fst_154_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_fst_154_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_143_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v_a_123_ = v___x_181_;
goto _start;
}
}
}
v___jp_159_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1));
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_148_);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_148_);
v___x_162_ = v_reuseFailAlloc_172_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_162_);
lean_ctor_set(v___x_136_, 0, v_fst_154_);
v___x_164_ = v___x_136_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_fst_154_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_171_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_164_);
v___x_166_ = v___x_132_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_fst_130_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_166_);
lean_ctor_set(v___x_126_, 0, v___x_160_);
v___x_168_ = v___x_126_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
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
lean_object* v___x_187_; 
if (v_isShared_142_ == 0)
{
v___x_187_ = v___x_141_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_snd_139_);
v___x_187_ = v_reuseFailAlloc_197_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_187_);
v___x_189_ = v___x_136_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_fst_134_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_196_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_189_);
v___x_191_ = v___x_132_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_fst_130_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_191_);
lean_ctor_set(v___x_126_, 0, v___x_143_);
v___x_193_ = v___x_126_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object* v_str1_205_, lean_object* v___x_206_, lean_object* v_str2_207_, lean_object* v_cutoff_208_, lean_object* v___x_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_205_, v___x_206_, v_str2_207_, v_cutoff_208_, v___x_209_, v_a_210_);
lean_dec(v___x_209_);
lean_dec(v_cutoff_208_);
lean_dec_ref(v_str2_207_);
lean_dec(v___x_206_);
lean_dec_ref(v_str1_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object* v_str2_212_, lean_object* v___x_213_, lean_object* v_str1_214_, lean_object* v_cutoff_215_, lean_object* v___x_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_snd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_297_; 
v_snd_218_ = lean_ctor_get(v_a_217_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_217_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_a_217_, 0);
lean_dec(v_unused_298_);
v___x_220_ = v_a_217_;
v_isShared_221_ = v_isSharedCheck_297_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snd_218_);
lean_dec(v_a_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_297_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_snd_222_; lean_object* v_snd_223_; lean_object* v_fst_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_295_; 
v_snd_222_ = lean_ctor_get(v_snd_218_, 1);
lean_inc(v_snd_222_);
v_snd_223_ = lean_ctor_get(v_snd_222_, 1);
lean_inc(v_snd_223_);
v_fst_224_ = lean_ctor_get(v_snd_218_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_snd_218_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_snd_218_, 1);
lean_dec(v_unused_296_);
v___x_226_ = v_snd_218_;
v_isShared_227_ = v_isSharedCheck_295_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_fst_224_);
lean_dec(v_snd_218_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_295_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_fst_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_293_; 
v_fst_228_ = lean_ctor_get(v_snd_222_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_snd_222_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_snd_222_, 1);
lean_dec(v_unused_294_);
v___x_230_ = v_snd_222_;
v_isShared_231_ = v_isSharedCheck_293_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_fst_228_);
lean_dec(v_snd_222_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_293_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_292_; 
v_fst_232_ = lean_ctor_get(v_snd_223_, 0);
v_snd_233_ = lean_ctor_get(v_snd_223_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_snd_223_);
if (v_isSharedCheck_292_ == 0)
{
v___x_235_ = v_snd_223_;
v_isShared_236_ = v_isSharedCheck_292_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_snd_233_);
lean_inc(v_fst_232_);
lean_dec(v_snd_223_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_292_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v_decide_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = lean_string_utf8_byte_size(v_str1_214_);
v_decide_239_ = lean_nat_dec_eq(v_fst_232_, v___x_238_);
if (v_decide_239_ == 0)
{
lean_object* v___x_240_; lean_object* v_i_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v_i_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_nat_add(v_snd_233_, v___x_240_);
lean_dec(v_snd_233_);
lean_inc(v___x_242_);
v___x_243_ = lean_array_fset(v_fst_228_, v_i_241_, v___x_242_);
v___x_244_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_244_);
lean_ctor_set(v___x_235_, 0, v___x_243_);
v___x_246_ = v___x_235_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_279_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v_fst_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_277_; 
v___x_247_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_212_, v___x_213_, v_fst_224_, v_fst_232_, v_str1_214_, v___x_246_);
v_fst_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_247_, 1);
lean_dec(v_unused_278_);
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_277_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_fst_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_277_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_252_ = lean_string_utf8_next_fast(v_str1_214_, v_fst_232_);
v___x_267_ = lean_array_get_size(v_fst_248_);
v___x_268_ = lean_nat_dec_lt(v_i_241_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v_fst_232_);
goto v___jp_253_;
}
else
{
if (v___x_268_ == 0)
{
lean_dec(v_fst_232_);
goto v___jp_253_;
}
else
{
size_t v___x_269_; size_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_267_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_215_, v_str1_214_, v_fst_232_, v___x_216_, v_fst_248_, v___x_269_, v___x_270_);
lean_dec(v_fst_232_);
if (v___x_271_ == 0)
{
goto v___jp_253_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_del_object(v___x_250_);
lean_del_object(v___x_230_);
lean_del_object(v___x_226_);
lean_dec(v_fst_224_);
lean_del_object(v___x_220_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_252_);
lean_ctor_set(v___x_272_, 1, v___x_242_);
lean_inc(v_fst_248_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_fst_248_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_fst_248_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_237_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_214_, v___x_213_, v_str2_212_, v_cutoff_215_, v___x_216_, v___x_275_);
return v___x_276_;
}
}
}
v___jp_253_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1));
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___x_242_);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_242_);
v___x_256_ = v_reuseFailAlloc_266_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_256_);
lean_ctor_set(v___x_230_, 0, v_fst_248_);
v___x_258_ = v___x_230_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_fst_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_265_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_258_);
v___x_260_ = v___x_226_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_fst_224_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_260_);
lean_ctor_set(v___x_220_, 0, v___x_254_);
v___x_262_ = v___x_220_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
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
if (v_isShared_236_ == 0)
{
v___x_281_ = v___x_235_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_snd_233_);
v___x_281_ = v_reuseFailAlloc_291_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_281_);
v___x_283_ = v___x_230_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_290_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_283_);
v___x_285_ = v___x_226_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_fst_224_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_285_);
lean_ctor_set(v___x_220_, 0, v___x_237_);
v___x_287_ = v___x_220_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_237_);
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
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* v_str1_306_, lean_object* v_str2_307_, lean_object* v_cutoff_308_){
_start:
{
lean_object* v_len1_309_; lean_object* v_len2_310_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_336_; uint8_t v___x_338_; 
v_len1_309_ = lean_string_length(v_str1_306_);
v_len2_310_ = lean_string_length(v_str2_307_);
v___x_338_ = lean_nat_dec_le(v_len1_309_, v_len2_310_);
if (v___x_338_ == 0)
{
v___y_336_ = v_len1_309_;
goto v___jp_335_;
}
else
{
v___y_336_ = v_len2_310_;
goto v___jp_335_;
}
v___jp_311_:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_nat_sub(v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec(v___y_312_);
v___x_315_ = lean_nat_dec_lt(v_cutoff_308_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_i_318_; lean_object* v_v1_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_fst_328_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_len2_310_, v___x_316_);
v_i_318_ = lean_unsigned_to_nat(0u);
lean_inc_n(v___x_317_, 2);
v_v1_319_ = lean_mk_array(v___x_317_, v_i_318_);
v___x_320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_320_, 0, v_i_318_);
lean_ctor_set(v___x_320_, 1, v___x_317_);
lean_ctor_set(v___x_320_, 2, v___x_316_);
lean_inc_ref(v_v1_319_);
v___x_321_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_320_, v_v1_319_, v_i_318_);
lean_dec_ref_known(v___x_320_, 3);
v___x_322_ = lean_box(0);
v___x_323_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_v1_319_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_321_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_322_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_307_, v___x_317_, v_str1_306_, v_cutoff_308_, v___x_314_, v___x_326_);
lean_dec(v___x_314_);
lean_dec(v___x_317_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
if (lean_obj_tag(v_fst_328_) == 0)
{
lean_object* v_snd_329_; lean_object* v_fst_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v___x_327_);
v_fst_330_ = lean_ctor_get(v_snd_329_, 0);
lean_inc(v_fst_330_);
lean_dec(v_snd_329_);
v___x_331_ = lean_array_fget(v_fst_330_, v_len2_310_);
lean_dec(v_fst_330_);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v_val_333_; 
lean_inc_ref(v_fst_328_);
lean_dec_ref(v___x_327_);
v_val_333_ = lean_ctor_get(v_fst_328_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_fst_328_, 1);
return v_val_333_;
}
}
else
{
lean_object* v___x_334_; 
lean_dec(v___x_314_);
v___x_334_ = lean_box(0);
return v___x_334_;
}
}
v___jp_335_:
{
uint8_t v___x_337_; 
v___x_337_ = lean_nat_dec_le(v_len1_309_, v_len2_310_);
if (v___x_337_ == 0)
{
v___y_312_ = v___y_336_;
v___y_313_ = v_len2_310_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___y_336_;
v___y_313_ = v_len1_309_;
goto v___jp_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* v_str1_339_, lean_object* v_str2_340_, lean_object* v_cutoff_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_EditDistance_levenshtein(v_str1_339_, v_str2_340_, v_cutoff_341_);
lean_dec(v_cutoff_341_);
lean_dec_ref(v_str2_340_);
lean_dec_ref(v_str1_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* v___x_343_, lean_object* v_range_344_, lean_object* v_b_345_, lean_object* v_i_346_, lean_object* v_hs_347_, lean_object* v_hl_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_344_, v_b_345_, v_i_346_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* v___x_350_, lean_object* v_range_351_, lean_object* v_b_352_, lean_object* v_i_353_, lean_object* v_hs_354_, lean_object* v_hl_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_350_, v_range_351_, v_b_352_, v_i_353_, v_hs_354_, v_hl_355_);
lean_dec_ref(v_range_351_);
lean_dec(v___x_350_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* v_str2_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v_str1_361_, lean_object* v_inst_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_357_, v___x_358_, v___x_359_, v___x_360_, v_str1_361_, v_a_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* v_str2_365_, lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v_str1_369_, lean_object* v_inst_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_365_, v___x_366_, v___x_367_, v___x_368_, v_str1_369_, v_inst_370_, v_a_371_);
lean_dec_ref(v_str1_369_);
lean_dec(v___x_368_);
lean_dec_ref(v___x_367_);
lean_dec(v___x_366_);
lean_dec_ref(v_str2_365_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* v_str2_373_, lean_object* v___x_374_, lean_object* v_str1_375_, lean_object* v_cutoff_376_, lean_object* v___x_377_, lean_object* v_inst_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_373_, v___x_374_, v_str1_375_, v_cutoff_376_, v___x_377_, v_a_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* v_str2_381_, lean_object* v___x_382_, lean_object* v_str1_383_, lean_object* v_cutoff_384_, lean_object* v___x_385_, lean_object* v_inst_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_381_, v___x_382_, v_str1_383_, v_cutoff_384_, v___x_385_, v_inst_386_, v_a_387_);
lean_dec(v___x_385_);
lean_dec(v_cutoff_384_);
lean_dec_ref(v_str1_383_);
lean_dec(v___x_382_);
lean_dec_ref(v_str2_381_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* v_str1_389_, lean_object* v___x_390_, lean_object* v_str2_391_, lean_object* v_cutoff_392_, lean_object* v___x_393_, lean_object* v_inst_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_389_, v___x_390_, v_str2_391_, v_cutoff_392_, v___x_393_, v_a_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* v_str1_397_, lean_object* v___x_398_, lean_object* v_str2_399_, lean_object* v_cutoff_400_, lean_object* v___x_401_, lean_object* v_inst_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_397_, v___x_398_, v_str2_399_, v_cutoff_400_, v___x_401_, v_inst_402_, v_a_403_);
lean_dec(v___x_401_);
lean_dec(v_cutoff_400_);
lean_dec_ref(v_str2_399_);
lean_dec(v___x_398_);
lean_dec_ref(v_str1_397_);
return v_res_404_;
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
