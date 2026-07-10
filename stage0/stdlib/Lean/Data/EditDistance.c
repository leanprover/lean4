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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_EditDistance_levenshtein___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_EditDistance_levenshtein___closed__0 = (const lean_object*)&l_Lean_EditDistance_levenshtein___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_string_utf8_byte_size(v_str2_14_);
v___x_31_ = lean_nat_dec_eq(v_fst_25_, v___x_30_);
if (v___x_31_ == 0)
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object* v_cutoff_78_, lean_object* v_as_79_, size_t v_i_80_, size_t v_stop_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_usize_dec_eq(v_i_80_, v_stop_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_array_uget_borrowed(v_as_79_, v_i_80_);
v___x_84_ = lean_nat_dec_lt(v_cutoff_78_, v___x_83_);
v___x_85_ = lean_bool_not(v___x_84_);
if (v___x_85_ == 0)
{
size_t v___x_86_; size_t v___x_87_; 
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_add(v_i_80_, v___x_86_);
v_i_80_ = v___x_87_;
goto _start;
}
else
{
return v___x_85_;
}
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* v_cutoff_90_, lean_object* v_as_91_, lean_object* v_i_92_, lean_object* v_stop_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_93_);
lean_dec(v_stop_93_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_90_, v_as_91_, v_i_boxed_94_, v_stop_boxed_95_);
lean_dec_ref(v_as_91_);
lean_dec(v_cutoff_90_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object* v_str1_100_, lean_object* v___x_101_, lean_object* v_str2_102_, lean_object* v_cutoff_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_snd_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_195_; 
v_snd_105_ = lean_ctor_get(v_a_104_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_a_104_, 0);
lean_dec(v_unused_196_);
v___x_107_ = v_a_104_;
v_isShared_108_ = v_isSharedCheck_195_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_snd_105_);
lean_dec(v_a_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_195_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_snd_109_; lean_object* v_snd_110_; lean_object* v_fst_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_193_; 
v_snd_109_ = lean_ctor_get(v_snd_105_, 1);
lean_inc(v_snd_109_);
v_snd_110_ = lean_ctor_get(v_snd_109_, 1);
lean_inc(v_snd_110_);
v_fst_111_ = lean_ctor_get(v_snd_105_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_snd_105_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v_snd_105_, 1);
lean_dec(v_unused_194_);
v___x_113_ = v_snd_105_;
v_isShared_114_ = v_isSharedCheck_193_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_fst_111_);
lean_dec(v_snd_105_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_193_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_191_; 
v_fst_115_ = lean_ctor_get(v_snd_109_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_snd_109_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_snd_109_, 1);
lean_dec(v_unused_192_);
v___x_117_ = v_snd_109_;
v_isShared_118_ = v_isSharedCheck_191_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_fst_115_);
lean_dec(v_snd_109_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_191_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_190_; 
v_fst_119_ = lean_ctor_get(v_snd_110_, 0);
v_snd_120_ = lean_ctor_get(v_snd_110_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_snd_110_);
if (v_isSharedCheck_190_ == 0)
{
v___x_122_ = v_snd_110_;
v_isShared_123_ = v_isSharedCheck_190_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_snd_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_190_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_box(0);
v___x_125_ = lean_string_utf8_byte_size(v_str1_100_);
v___x_126_ = lean_nat_dec_eq(v_fst_119_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v_i_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v_i_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_add(v_snd_120_, v___x_127_);
lean_dec(v_snd_120_);
lean_inc(v___x_129_);
v___x_130_ = lean_array_fset(v_fst_115_, v_i_128_, v___x_129_);
v___x_131_ = lean_nat_mod(v_i_128_, v___x_101_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_131_);
lean_ctor_set(v___x_122_, 0, v_i_128_);
v___x_133_ = v___x_122_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_i_128_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_177_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_133_);
lean_ctor_set(v___x_117_, 0, v___x_130_);
v___x_135_ = v___x_117_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_176_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v_fst_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_174_; 
v___x_136_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_102_, v___x_101_, v_fst_111_, v_fst_119_, v_str1_100_, v___x_135_);
v_fst_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_136_, 1);
lean_dec(v_unused_175_);
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_174_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_fst_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_174_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; uint8_t v___y_143_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_141_ = lean_string_utf8_next_fast(v_str1_100_, v_fst_119_);
lean_dec(v_fst_119_);
v___x_166_ = lean_array_get_size(v_fst_137_);
v___x_167_ = lean_nat_dec_lt(v_i_128_, v___x_166_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_bool_not(v___x_167_);
v___y_143_ = v___x_168_;
goto v___jp_142_;
}
else
{
if (v___x_167_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = lean_bool_not(v___x_167_);
v___y_143_ = v___x_169_;
goto v___jp_142_;
}
else
{
size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_170_ = ((size_t)0ULL);
v___x_171_ = lean_usize_of_nat(v___x_166_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_103_, v_fst_137_, v___x_170_, v___x_171_);
v___x_173_ = lean_bool_not(v___x_172_);
v___y_143_ = v___x_173_;
goto v___jp_142_;
}
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v_fst_111_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_129_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_145_ = v___x_139_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_129_);
v___x_145_ = v_reuseFailAlloc_154_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
lean_inc(v_fst_137_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_145_);
lean_ctor_set(v___x_113_, 0, v_fst_137_);
v___x_147_ = v___x_113_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_153_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_147_);
lean_ctor_set(v___x_107_, 0, v_fst_137_);
v___x_149_ = v___x_107_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_124_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v_a_104_ = v___x_150_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_129_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_157_ = v___x_139_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_129_);
v___x_157_ = v_reuseFailAlloc_165_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_157_);
lean_ctor_set(v___x_113_, 0, v_fst_137_);
v___x_159_ = v___x_113_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_164_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_161_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_159_);
lean_ctor_set(v___x_107_, 0, v_fst_111_);
v___x_161_ = v___x_107_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_159_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_155_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
return v___x_162_;
}
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
lean_object* v___x_179_; 
if (v_isShared_123_ == 0)
{
v___x_179_ = v___x_122_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_snd_120_);
v___x_179_ = v_reuseFailAlloc_189_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_181_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_179_);
v___x_181_ = v___x_117_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_188_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_181_);
v___x_183_ = v___x_113_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_187_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_185_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_183_);
lean_ctor_set(v___x_107_, 0, v___x_124_);
v___x_185_ = v___x_107_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object* v_str1_197_, lean_object* v___x_198_, lean_object* v_str2_199_, lean_object* v_cutoff_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_197_, v___x_198_, v_str2_199_, v_cutoff_200_, v_a_201_);
lean_dec(v_cutoff_200_);
lean_dec_ref(v_str2_199_);
lean_dec(v___x_198_);
lean_dec_ref(v_str1_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object* v_str2_203_, lean_object* v___x_204_, lean_object* v_str1_205_, lean_object* v_cutoff_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_snd_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_298_; 
v_snd_208_ = lean_ctor_get(v_a_207_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_207_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v_a_207_, 0);
lean_dec(v_unused_299_);
v___x_210_ = v_a_207_;
v_isShared_211_ = v_isSharedCheck_298_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_snd_208_);
lean_dec(v_a_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_298_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_snd_212_; lean_object* v_snd_213_; lean_object* v_fst_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_296_; 
v_snd_212_ = lean_ctor_get(v_snd_208_, 1);
lean_inc(v_snd_212_);
v_snd_213_ = lean_ctor_get(v_snd_212_, 1);
lean_inc(v_snd_213_);
v_fst_214_ = lean_ctor_get(v_snd_208_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_snd_208_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_snd_208_, 1);
lean_dec(v_unused_297_);
v___x_216_ = v_snd_208_;
v_isShared_217_ = v_isSharedCheck_296_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_fst_214_);
lean_dec(v_snd_208_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_296_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_fst_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_294_; 
v_fst_218_ = lean_ctor_get(v_snd_212_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_snd_212_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_snd_212_, 1);
lean_dec(v_unused_295_);
v___x_220_ = v_snd_212_;
v_isShared_221_ = v_isSharedCheck_294_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_fst_218_);
lean_dec(v_snd_212_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_294_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_293_; 
v_fst_222_ = lean_ctor_get(v_snd_213_, 0);
v_snd_223_ = lean_ctor_get(v_snd_213_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_snd_213_);
if (v_isSharedCheck_293_ == 0)
{
v___x_225_ = v_snd_213_;
v_isShared_226_ = v_isSharedCheck_293_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_inc(v_fst_222_);
lean_dec(v_snd_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_293_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_227_ = lean_box(0);
v___x_228_ = lean_string_utf8_byte_size(v_str1_205_);
v___x_229_ = lean_nat_dec_eq(v_fst_222_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v_i_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v_i_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_add(v_snd_223_, v___x_230_);
lean_dec(v_snd_223_);
lean_inc(v___x_232_);
v___x_233_ = lean_array_fset(v_fst_218_, v_i_231_, v___x_232_);
v___x_234_ = lean_nat_mod(v_i_231_, v___x_204_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_234_);
lean_ctor_set(v___x_225_, 0, v_i_231_);
v___x_236_ = v___x_225_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_i_231_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_280_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_236_);
lean_ctor_set(v___x_220_, 0, v___x_233_);
v___x_238_ = v___x_220_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_279_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v_fst_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_277_; 
v___x_239_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_203_, v___x_204_, v_fst_214_, v_fst_222_, v_str1_205_, v___x_238_);
v_fst_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_239_, 1);
lean_dec(v_unused_278_);
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_277_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_fst_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_277_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint8_t v___y_246_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_244_ = lean_string_utf8_next_fast(v_str1_205_, v_fst_222_);
lean_dec(v_fst_222_);
v___x_269_ = lean_array_get_size(v_fst_240_);
v___x_270_ = lean_nat_dec_lt(v_i_231_, v___x_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = lean_bool_not(v___x_270_);
v___y_246_ = v___x_271_;
goto v___jp_245_;
}
else
{
if (v___x_270_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = lean_bool_not(v___x_270_);
v___y_246_ = v___x_272_;
goto v___jp_245_;
}
else
{
size_t v___x_273_; size_t v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___x_269_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_206_, v_fst_240_, v___x_273_, v___x_274_);
v___x_276_ = lean_bool_not(v___x_275_);
v___y_246_ = v___x_276_;
goto v___jp_245_;
}
}
v___jp_245_:
{
if (v___y_246_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_fst_214_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_232_);
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_232_);
v___x_248_ = v_reuseFailAlloc_257_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
lean_inc(v_fst_240_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_248_);
lean_ctor_set(v___x_216_, 0, v_fst_240_);
v___x_250_ = v___x_216_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_256_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_250_);
lean_ctor_set(v___x_210_, 0, v_fst_240_);
v___x_252_ = v___x_210_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_227_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_205_, v___x_204_, v_str2_203_, v_cutoff_206_, v___x_253_);
return v___x_254_;
}
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_232_);
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_260_ = v___x_242_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_232_);
v___x_260_ = v_reuseFailAlloc_268_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_260_);
lean_ctor_set(v___x_216_, 0, v_fst_240_);
v___x_262_ = v___x_216_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_267_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_262_);
lean_ctor_set(v___x_210_, 0, v_fst_214_);
v___x_264_ = v___x_210_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_258_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
return v___x_265_;
}
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
lean_object* v___x_282_; 
if (v_isShared_226_ == 0)
{
v___x_282_ = v___x_225_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_222_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_223_);
v___x_282_ = v_reuseFailAlloc_292_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_282_);
v___x_284_ = v___x_220_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_fst_218_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_291_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_284_);
v___x_286_ = v___x_216_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_290_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_286_);
lean_ctor_set(v___x_210_, 0, v___x_227_);
v___x_288_ = v___x_210_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object* v_str2_300_, lean_object* v___x_301_, lean_object* v_str1_302_, lean_object* v_cutoff_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_300_, v___x_301_, v_str1_302_, v_cutoff_303_, v_a_304_);
lean_dec(v_cutoff_303_);
lean_dec_ref(v_str1_302_);
lean_dec(v___x_301_);
lean_dec_ref(v_str2_300_);
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
lean_dec(v___x_316_);
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
v___x_329_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_309_, v___x_319_, v_str1_308_, v_cutoff_310_, v___x_328_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* v_str2_375_, lean_object* v___x_376_, lean_object* v_str1_377_, lean_object* v_cutoff_378_, lean_object* v_inst_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_375_, v___x_376_, v_str1_377_, v_cutoff_378_, v_a_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* v_str2_382_, lean_object* v___x_383_, lean_object* v_str1_384_, lean_object* v_cutoff_385_, lean_object* v_inst_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_382_, v___x_383_, v_str1_384_, v_cutoff_385_, v_inst_386_, v_a_387_);
lean_dec(v_cutoff_385_);
lean_dec_ref(v_str1_384_);
lean_dec(v___x_383_);
lean_dec_ref(v_str2_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* v_str1_389_, lean_object* v___x_390_, lean_object* v_str2_391_, lean_object* v_cutoff_392_, lean_object* v_inst_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_389_, v___x_390_, v_str2_391_, v_cutoff_392_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* v_str1_396_, lean_object* v___x_397_, lean_object* v_str2_398_, lean_object* v_cutoff_399_, lean_object* v_inst_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_396_, v___x_397_, v_str2_398_, v_cutoff_399_, v_inst_400_, v_a_401_);
lean_dec(v_cutoff_399_);
lean_dec_ref(v_str2_398_);
lean_dec(v___x_397_);
lean_dec_ref(v_str1_396_);
return v_res_402_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
