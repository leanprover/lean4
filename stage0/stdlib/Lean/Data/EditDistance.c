// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: public import Init.Data.String.Basic import Init.Data.Vector.Basic import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Init.Data.Range import Init.While
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_EditDistance_levenshtein___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_EditDistance_levenshtein___closed__0 = (const lean_object*)&l_Lean_EditDistance_levenshtein___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* v_str2_14_, lean_object* v___x_15_, lean_object* v___x_16_, lean_object* v___x_17_, lean_object* v_str1_18_, lean_object* v_b_19_){
_start:
{
lean_object* v_snd_20_; lean_object* v_fst_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_70_; 
v_snd_20_ = lean_ctor_get(v_b_19_, 1);
v_fst_21_ = lean_ctor_get(v_b_19_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_b_19_);
if (v_isSharedCheck_70_ == 0)
{
v___x_23_ = v_b_19_;
v_isShared_24_ = v_isSharedCheck_70_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_snd_20_);
lean_inc(v_fst_21_);
lean_dec(v_b_19_);
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
v_b_19_ = v___x_42_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* v_str2_71_, lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_str1_75_, lean_object* v_b_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_71_, v___x_72_, v___x_73_, v___x_74_, v_str1_75_, v_b_76_);
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
uint8_t v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = 1;
v___x_84_ = lean_array_uget_borrowed(v_as_79_, v_i_80_);
v___x_85_ = lean_nat_dec_lt(v_cutoff_78_, v___x_84_);
if (v___x_85_ == 0)
{
return v___x_83_;
}
else
{
if (v___x_82_ == 0)
{
size_t v___x_86_; size_t v___x_87_; 
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_add(v_i_80_, v___x_86_);
v_i_80_ = v___x_87_;
goto _start;
}
else
{
return v___x_83_;
}
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* v_str1_100_, lean_object* v___x_101_, lean_object* v_str2_102_, lean_object* v_cutoff_103_, lean_object* v_b_104_){
_start:
{
lean_object* v_snd_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_185_; 
v_snd_105_ = lean_ctor_get(v_b_104_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_b_104_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_b_104_, 0);
lean_dec(v_unused_186_);
v___x_107_ = v_b_104_;
v_isShared_108_ = v_isSharedCheck_185_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_snd_105_);
lean_dec(v_b_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_185_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_snd_109_; lean_object* v_snd_110_; lean_object* v_fst_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_183_; 
v_snd_109_ = lean_ctor_get(v_snd_105_, 1);
lean_inc(v_snd_109_);
v_snd_110_ = lean_ctor_get(v_snd_109_, 1);
lean_inc(v_snd_110_);
v_fst_111_ = lean_ctor_get(v_snd_105_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_snd_105_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_snd_105_, 1);
lean_dec(v_unused_184_);
v___x_113_ = v_snd_105_;
v_isShared_114_ = v_isSharedCheck_183_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_fst_111_);
lean_dec(v_snd_105_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_183_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_181_; 
v_fst_115_ = lean_ctor_get(v_snd_109_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_snd_109_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_snd_109_, 1);
lean_dec(v_unused_182_);
v___x_117_ = v_snd_109_;
v_isShared_118_ = v_isSharedCheck_181_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_fst_115_);
lean_dec(v_snd_109_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_181_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_180_; 
v_fst_119_ = lean_ctor_get(v_snd_110_, 0);
v_snd_120_ = lean_ctor_get(v_snd_110_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_snd_110_);
if (v_isSharedCheck_180_ == 0)
{
v___x_122_ = v_snd_110_;
v_isShared_123_ = v_isSharedCheck_180_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_snd_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_180_;
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
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_i_128_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_167_;
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
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_166_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v_fst_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_164_; 
v___x_136_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_102_, v___x_101_, v_fst_111_, v_fst_119_, v_str1_100_, v___x_135_);
v_fst_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v___x_136_, 1);
lean_dec(v_unused_165_);
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_164_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_fst_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_164_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_141_ = lean_string_utf8_next_fast(v_str1_100_, v_fst_119_);
lean_dec(v_fst_119_);
v___x_154_ = lean_array_get_size(v_fst_137_);
v___x_155_ = lean_nat_dec_lt(v_i_128_, v___x_154_);
if (v___x_155_ == 0)
{
goto v___jp_142_;
}
else
{
if (v___x_155_ == 0)
{
goto v___jp_142_;
}
else
{
size_t v___x_156_; size_t v___x_157_; uint8_t v___x_158_; 
v___x_156_ = ((size_t)0ULL);
v___x_157_ = lean_usize_of_nat(v___x_154_);
v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_103_, v_fst_137_, v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
goto v___jp_142_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_del_object(v___x_139_);
lean_del_object(v___x_113_);
lean_dec(v_fst_111_);
lean_del_object(v___x_107_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_141_);
lean_ctor_set(v___x_159_, 1, v___x_129_);
lean_inc(v_fst_137_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_fst_137_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_fst_137_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_124_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v_b_104_ = v___x_162_;
goto _start;
}
}
}
v___jp_142_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_129_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_145_ = v___x_139_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_129_);
v___x_145_ = v_reuseFailAlloc_153_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_145_);
lean_ctor_set(v___x_113_, 0, v_fst_137_);
v___x_147_ = v___x_113_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_152_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_147_);
lean_ctor_set(v___x_107_, 0, v_fst_111_);
v___x_149_ = v___x_107_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_143_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
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
lean_object* v___x_169_; 
if (v_isShared_123_ == 0)
{
v___x_169_ = v___x_122_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_snd_120_);
v___x_169_ = v_reuseFailAlloc_179_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_169_);
v___x_171_ = v___x_117_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_178_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_171_);
v___x_173_ = v___x_113_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_171_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_173_);
lean_ctor_set(v___x_107_, 0, v___x_124_);
v___x_175_ = v___x_107_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* v_str1_187_, lean_object* v___x_188_, lean_object* v_str2_189_, lean_object* v_cutoff_190_, lean_object* v_b_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_187_, v___x_188_, v_str2_189_, v_cutoff_190_, v_b_191_);
lean_dec(v_cutoff_190_);
lean_dec_ref(v_str2_189_);
lean_dec(v___x_188_);
lean_dec_ref(v_str1_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* v_str2_193_, lean_object* v___x_194_, lean_object* v_str1_195_, lean_object* v_cutoff_196_, lean_object* v_b_197_){
_start:
{
lean_object* v_snd_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_278_; 
v_snd_198_ = lean_ctor_get(v_b_197_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_b_197_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_b_197_, 0);
lean_dec(v_unused_279_);
v___x_200_ = v_b_197_;
v_isShared_201_ = v_isSharedCheck_278_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_snd_198_);
lean_dec(v_b_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_278_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_snd_202_; lean_object* v_snd_203_; lean_object* v_fst_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_276_; 
v_snd_202_ = lean_ctor_get(v_snd_198_, 1);
lean_inc(v_snd_202_);
v_snd_203_ = lean_ctor_get(v_snd_202_, 1);
lean_inc(v_snd_203_);
v_fst_204_ = lean_ctor_get(v_snd_198_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_snd_198_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_snd_198_, 1);
lean_dec(v_unused_277_);
v___x_206_ = v_snd_198_;
v_isShared_207_ = v_isSharedCheck_276_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_fst_204_);
lean_dec(v_snd_198_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_276_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_fst_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_274_; 
v_fst_208_ = lean_ctor_get(v_snd_202_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_snd_202_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v_snd_202_, 1);
lean_dec(v_unused_275_);
v___x_210_ = v_snd_202_;
v_isShared_211_ = v_isSharedCheck_274_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_fst_208_);
lean_dec(v_snd_202_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_274_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_273_; 
v_fst_212_ = lean_ctor_get(v_snd_203_, 0);
v_snd_213_ = lean_ctor_get(v_snd_203_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_snd_203_);
if (v_isSharedCheck_273_ == 0)
{
v___x_215_ = v_snd_203_;
v_isShared_216_ = v_isSharedCheck_273_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snd_213_);
lean_inc(v_fst_212_);
lean_dec(v_snd_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_273_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_string_utf8_byte_size(v_str1_195_);
v___x_219_ = lean_nat_dec_eq(v_fst_212_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v_i_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_220_ = lean_unsigned_to_nat(1u);
v_i_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_nat_add(v_snd_213_, v___x_220_);
lean_dec(v_snd_213_);
lean_inc(v___x_222_);
v___x_223_ = lean_array_fset(v_fst_208_, v_i_221_, v___x_222_);
v___x_224_ = lean_nat_mod(v_i_221_, v___x_194_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_224_);
lean_ctor_set(v___x_215_, 0, v_i_221_);
v___x_226_ = v___x_215_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_i_221_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_224_);
v___x_226_ = v_reuseFailAlloc_260_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_226_);
lean_ctor_set(v___x_210_, 0, v___x_223_);
v___x_228_ = v___x_210_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_259_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v_fst_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_257_; 
v___x_229_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_193_, v___x_194_, v_fst_204_, v_fst_212_, v_str1_195_, v___x_228_);
v_fst_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_229_, 1);
lean_dec(v_unused_258_);
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_257_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_fst_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_257_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_234_ = lean_string_utf8_next_fast(v_str1_195_, v_fst_212_);
lean_dec(v_fst_212_);
v___x_247_ = lean_array_get_size(v_fst_230_);
v___x_248_ = lean_nat_dec_lt(v_i_221_, v___x_247_);
if (v___x_248_ == 0)
{
goto v___jp_235_;
}
else
{
if (v___x_248_ == 0)
{
goto v___jp_235_;
}
else
{
size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; 
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_247_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_196_, v_fst_230_, v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
goto v___jp_235_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_del_object(v___x_232_);
lean_del_object(v___x_206_);
lean_dec(v_fst_204_);
lean_del_object(v___x_200_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_234_);
lean_ctor_set(v___x_252_, 1, v___x_222_);
lean_inc(v_fst_230_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_fst_230_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_fst_230_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_217_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_195_, v___x_194_, v_str2_193_, v_cutoff_196_, v___x_255_);
return v___x_256_;
}
}
}
v___jp_235_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_222_);
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_222_);
v___x_238_ = v_reuseFailAlloc_246_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_238_);
lean_ctor_set(v___x_206_, 0, v_fst_230_);
v___x_240_ = v___x_206_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_245_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v___x_240_);
lean_ctor_set(v___x_200_, 0, v_fst_204_);
v___x_242_ = v___x_200_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_236_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
return v___x_243_;
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
lean_object* v___x_262_; 
if (v_isShared_216_ == 0)
{
v___x_262_ = v___x_215_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_fst_212_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_snd_213_);
v___x_262_ = v_reuseFailAlloc_272_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_262_);
v___x_264_ = v___x_210_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_271_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_264_);
v___x_266_ = v___x_206_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_270_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v___x_266_);
lean_ctor_set(v___x_200_, 0, v___x_217_);
v___x_268_ = v___x_200_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* v_str2_280_, lean_object* v___x_281_, lean_object* v_str1_282_, lean_object* v_cutoff_283_, lean_object* v_b_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_280_, v___x_281_, v_str1_282_, v_cutoff_283_, v_b_284_);
lean_dec(v_cutoff_283_);
lean_dec_ref(v_str1_282_);
lean_dec(v___x_281_);
lean_dec_ref(v_str2_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* v_str1_288_, lean_object* v_str2_289_, lean_object* v_cutoff_290_){
_start:
{
lean_object* v_len1_291_; lean_object* v_len2_292_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_318_; uint8_t v___x_320_; 
v_len1_291_ = lean_string_length(v_str1_288_);
v_len2_292_ = lean_string_length(v_str2_289_);
v___x_320_ = lean_nat_dec_le(v_len1_291_, v_len2_292_);
if (v___x_320_ == 0)
{
v___y_318_ = v_len1_291_;
goto v___jp_317_;
}
else
{
v___y_318_ = v_len2_292_;
goto v___jp_317_;
}
v___jp_293_:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_nat_sub(v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v___y_294_);
v___x_297_ = lean_nat_dec_lt(v_cutoff_290_, v___x_296_);
lean_dec(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_i_300_; lean_object* v_v1_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_fst_310_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_len2_292_, v___x_298_);
v_i_300_ = lean_unsigned_to_nat(0u);
lean_inc_n(v___x_299_, 2);
v_v1_301_ = lean_mk_array(v___x_299_, v_i_300_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v_i_300_);
lean_ctor_set(v___x_302_, 1, v___x_299_);
lean_ctor_set(v___x_302_, 2, v___x_298_);
lean_inc_ref(v_v1_301_);
v___x_303_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_302_, v_v1_301_, v_i_300_);
lean_dec_ref(v___x_302_);
v___x_304_ = lean_box(0);
v___x_305_ = ((lean_object*)(l_Lean_EditDistance_levenshtein___closed__0));
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_v1_301_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_303_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_289_, v___x_299_, v_str1_288_, v_cutoff_290_, v___x_308_);
lean_dec(v___x_299_);
v_fst_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_fst_310_);
if (lean_obj_tag(v_fst_310_) == 0)
{
lean_object* v_snd_311_; lean_object* v_fst_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_snd_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_311_);
lean_dec_ref(v___x_309_);
v_fst_312_ = lean_ctor_get(v_snd_311_, 0);
lean_inc(v_fst_312_);
lean_dec(v_snd_311_);
v___x_313_ = lean_array_fget(v_fst_312_, v_len2_292_);
lean_dec(v_fst_312_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v_val_315_; 
lean_dec_ref(v___x_309_);
v_val_315_ = lean_ctor_get(v_fst_310_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v_fst_310_);
return v_val_315_;
}
}
else
{
lean_object* v___x_316_; 
v___x_316_ = lean_box(0);
return v___x_316_;
}
}
v___jp_317_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_le(v_len1_291_, v_len2_292_);
if (v___x_319_ == 0)
{
v___y_294_ = v___y_318_;
v___y_295_ = v_len2_292_;
goto v___jp_293_;
}
else
{
v___y_294_ = v___y_318_;
v___y_295_ = v_len1_291_;
goto v___jp_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* v_str1_321_, lean_object* v_str2_322_, lean_object* v_cutoff_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_EditDistance_levenshtein(v_str1_321_, v_str2_322_, v_cutoff_323_);
lean_dec(v_cutoff_323_);
lean_dec_ref(v_str2_322_);
lean_dec_ref(v_str1_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* v___x_325_, lean_object* v_range_326_, lean_object* v_b_327_, lean_object* v_i_328_, lean_object* v_hs_329_, lean_object* v_hl_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_326_, v_b_327_, v_i_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* v___x_332_, lean_object* v_range_333_, lean_object* v_b_334_, lean_object* v_i_335_, lean_object* v_hs_336_, lean_object* v_hl_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_332_, v_range_333_, v_b_334_, v_i_335_, v_hs_336_, v_hl_337_);
lean_dec_ref(v_range_333_);
lean_dec(v___x_332_);
return v_res_338_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
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
