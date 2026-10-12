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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object* v_cutoff_78_, lean_object* v_str1_79_, lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v_as_82_, size_t v_i_83_, size_t v_stop_84_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cutoff_78_ = stack[0].m_obj;
lean_object* v_str1_79_ = stack[1].m_obj;
lean_object* v___x_80_ = stack[2].m_obj;
lean_object* v___x_81_ = stack[3].m_obj;
lean_object* v_as_82_ = stack[4].m_obj;
size_t v_i_83_ = stack[5].m_num;
size_t v_stop_84_ = stack[6].m_num;
uint8_t v_res_103_;
v_res_103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_78_, v_str1_79_, v___x_80_, v___x_81_, v_as_82_, v_i_83_, v_stop_84_);
stack->m_num = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* v_cutoff_104_, lean_object* v_str1_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_as_108_, lean_object* v_i_109_, lean_object* v_stop_110_){
_start:
{
size_t v_i_boxed_111_; size_t v_stop_boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_i_boxed_111_ = lean_unbox_usize(v_i_109_);
lean_dec(v_i_109_);
v_stop_boxed_112_ = lean_unbox_usize(v_stop_110_);
lean_dec(v_stop_110_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_104_, v_str1_105_, v___x_106_, v___x_107_, v_as_108_, v_i_boxed_111_, v_stop_boxed_112_);
lean_dec_ref(v_as_108_);
lean_dec(v___x_107_);
lean_dec(v___x_106_);
lean_dec_ref(v_str1_105_);
lean_dec(v_cutoff_104_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(lean_object* v_str1_119_, lean_object* v___x_120_, lean_object* v_str2_121_, lean_object* v_cutoff_122_, lean_object* v___x_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_204_; 
v_snd_125_ = lean_ctor_get(v_a_124_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_124_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_a_124_, 0);
lean_dec(v_unused_205_);
v___x_127_ = v_a_124_;
v_isShared_128_ = v_isSharedCheck_204_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_dec(v_a_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_204_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_snd_129_; lean_object* v_snd_130_; lean_object* v_fst_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_202_; 
v_snd_129_ = lean_ctor_get(v_snd_125_, 1);
lean_inc(v_snd_129_);
v_snd_130_ = lean_ctor_get(v_snd_129_, 1);
lean_inc(v_snd_130_);
v_fst_131_ = lean_ctor_get(v_snd_125_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_snd_125_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_snd_125_, 1);
lean_dec(v_unused_203_);
v___x_133_ = v_snd_125_;
v_isShared_134_ = v_isSharedCheck_202_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_fst_131_);
lean_dec(v_snd_125_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_202_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_fst_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_200_; 
v_fst_135_ = lean_ctor_get(v_snd_129_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_snd_129_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_snd_129_, 1);
lean_dec(v_unused_201_);
v___x_137_ = v_snd_129_;
v_isShared_138_ = v_isSharedCheck_200_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_fst_135_);
lean_dec(v_snd_129_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_200_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_199_; 
v_fst_139_ = lean_ctor_get(v_snd_130_, 0);
v_snd_140_ = lean_ctor_get(v_snd_130_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_snd_130_);
if (v_isSharedCheck_199_ == 0)
{
v___x_142_ = v_snd_130_;
v_isShared_143_ = v_isSharedCheck_199_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_snd_140_);
lean_inc(v_fst_139_);
lean_dec(v_snd_130_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_199_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v_decide_146_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_string_utf8_byte_size(v_str1_119_);
v_decide_146_ = lean_nat_dec_eq(v_fst_139_, v___x_145_);
if (v_decide_146_ == 0)
{
lean_object* v___x_147_; lean_object* v_i_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v_i_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_add(v_snd_140_, v___x_147_);
lean_dec(v_snd_140_);
lean_inc(v___x_149_);
v___x_150_ = lean_array_fset(v_fst_135_, v_i_148_, v___x_149_);
v___x_151_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_151_);
lean_ctor_set(v___x_142_, 0, v___x_150_);
v___x_153_ = v___x_142_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_186_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v_fst_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_184_; 
v___x_154_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_121_, v___x_120_, v_fst_131_, v_fst_139_, v_str1_119_, v___x_153_);
v_fst_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_154_, 1);
lean_dec(v_unused_185_);
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_184_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_fst_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_184_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_159_ = lean_string_utf8_next_fast(v_str1_119_, v_fst_139_);
v___x_174_ = lean_array_get_size(v_fst_155_);
v___x_175_ = lean_nat_dec_lt(v_i_148_, v___x_174_);
if (v___x_175_ == 0)
{
lean_dec(v_fst_139_);
goto v___jp_160_;
}
else
{
if (v___x_175_ == 0)
{
lean_dec(v_fst_139_);
goto v___jp_160_;
}
else
{
size_t v___x_176_; size_t v___x_177_; uint8_t v___x_178_; 
v___x_176_ = ((size_t)0ULL);
v___x_177_ = lean_usize_of_nat(v___x_174_);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_122_, v_str1_119_, v_fst_139_, v___x_123_, v_fst_155_, v___x_176_, v___x_177_);
lean_dec(v_fst_139_);
if (v___x_178_ == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_del_object(v___x_157_);
lean_del_object(v___x_137_);
lean_del_object(v___x_133_);
lean_dec(v_fst_131_);
lean_del_object(v___x_127_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_159_);
lean_ctor_set(v___x_179_, 1, v___x_149_);
lean_inc(v_fst_155_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_fst_155_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_fst_155_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_144_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v_a_124_ = v___x_182_;
goto _start;
}
}
}
v___jp_160_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1));
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_149_);
lean_ctor_set(v___x_157_, 0, v___x_159_);
v___x_163_ = v___x_157_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_149_);
v___x_163_ = v_reuseFailAlloc_173_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_163_);
lean_ctor_set(v___x_137_, 0, v_fst_155_);
v___x_165_ = v___x_137_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_fst_155_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_172_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_165_);
v___x_167_ = v___x_133_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_169_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_167_);
lean_ctor_set(v___x_127_, 0, v___x_161_);
v___x_169_ = v___x_127_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
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
lean_object* v___x_188_; 
if (v_isShared_143_ == 0)
{
v___x_188_ = v___x_142_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_fst_139_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_snd_140_);
v___x_188_ = v_reuseFailAlloc_198_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_188_);
v___x_190_ = v___x_137_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_fst_135_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_197_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_190_);
v___x_192_ = v___x_133_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_192_);
lean_ctor_set(v___x_127_, 0, v___x_144_);
v___x_194_ = v___x_127_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(lean_object* v_str1_206_, lean_object* v___x_207_, lean_object* v_str2_208_, lean_object* v_cutoff_209_, lean_object* v___x_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_206_, v___x_207_, v_str2_208_, v_cutoff_209_, v___x_210_, v_a_211_);
lean_dec(v___x_210_);
lean_dec(v_cutoff_209_);
lean_dec_ref(v_str2_208_);
lean_dec(v___x_207_);
lean_dec_ref(v_str1_206_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(lean_object* v_str2_213_, lean_object* v___x_214_, lean_object* v_str1_215_, lean_object* v_cutoff_216_, lean_object* v___x_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_snd_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_298_; 
v_snd_219_ = lean_ctor_get(v_a_218_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_218_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v_a_218_, 0);
lean_dec(v_unused_299_);
v___x_221_ = v_a_218_;
v_isShared_222_ = v_isSharedCheck_298_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snd_219_);
lean_dec(v_a_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_298_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_snd_223_; lean_object* v_snd_224_; lean_object* v_fst_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_296_; 
v_snd_223_ = lean_ctor_get(v_snd_219_, 1);
lean_inc(v_snd_223_);
v_snd_224_ = lean_ctor_get(v_snd_223_, 1);
lean_inc(v_snd_224_);
v_fst_225_ = lean_ctor_get(v_snd_219_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_snd_219_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_snd_219_, 1);
lean_dec(v_unused_297_);
v___x_227_ = v_snd_219_;
v_isShared_228_ = v_isSharedCheck_296_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_fst_225_);
lean_dec(v_snd_219_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_296_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_fst_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_294_; 
v_fst_229_ = lean_ctor_get(v_snd_223_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_snd_223_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_snd_223_, 1);
lean_dec(v_unused_295_);
v___x_231_ = v_snd_223_;
v_isShared_232_ = v_isSharedCheck_294_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_fst_229_);
lean_dec(v_snd_223_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_294_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_293_; 
v_fst_233_ = lean_ctor_get(v_snd_224_, 0);
v_snd_234_ = lean_ctor_get(v_snd_224_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_snd_224_);
if (v_isSharedCheck_293_ == 0)
{
v___x_236_ = v_snd_224_;
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_snd_234_);
lean_inc(v_fst_233_);
lean_dec(v_snd_224_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_293_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v_decide_240_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_string_utf8_byte_size(v_str1_215_);
v_decide_240_ = lean_nat_dec_eq(v_fst_233_, v___x_239_);
if (v_decide_240_ == 0)
{
lean_object* v___x_241_; lean_object* v_i_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v_i_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_nat_add(v_snd_234_, v___x_241_);
lean_dec(v_snd_234_);
lean_inc(v___x_243_);
v___x_244_ = lean_array_fset(v_fst_229_, v_i_242_, v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v___x_245_);
lean_ctor_set(v___x_236_, 0, v___x_244_);
v___x_247_ = v___x_236_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_280_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v_fst_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_278_; 
v___x_248_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_213_, v___x_214_, v_fst_225_, v_fst_233_, v_str1_215_, v___x_247_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_248_, 1);
lean_dec(v_unused_279_);
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_278_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_fst_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_278_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_253_ = lean_string_utf8_next_fast(v_str1_215_, v_fst_233_);
v___x_268_ = lean_array_get_size(v_fst_249_);
v___x_269_ = lean_nat_dec_lt(v_i_242_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v_fst_233_);
goto v___jp_254_;
}
else
{
if (v___x_269_ == 0)
{
lean_dec(v_fst_233_);
goto v___jp_254_;
}
else
{
size_t v___x_270_; size_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_268_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_216_, v_str1_215_, v_fst_233_, v___x_217_, v_fst_249_, v___x_270_, v___x_271_);
lean_dec(v_fst_233_);
if (v___x_272_ == 0)
{
goto v___jp_254_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_del_object(v___x_251_);
lean_del_object(v___x_231_);
lean_del_object(v___x_227_);
lean_dec(v_fst_225_);
lean_del_object(v___x_221_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_253_);
lean_ctor_set(v___x_273_, 1, v___x_243_);
lean_inc(v_fst_249_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_fst_249_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_fst_249_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_238_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_215_, v___x_214_, v_str2_213_, v_cutoff_216_, v___x_217_, v___x_276_);
return v___x_277_;
}
}
}
v___jp_254_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__1));
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_243_);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_243_);
v___x_257_ = v_reuseFailAlloc_267_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_257_);
lean_ctor_set(v___x_231_, 0, v_fst_249_);
v___x_259_ = v___x_231_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_266_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_259_);
v___x_261_ = v___x_227_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_fst_225_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_261_);
lean_ctor_set(v___x_221_, 0, v___x_255_);
v___x_263_ = v___x_221_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
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
if (v_isShared_237_ == 0)
{
v___x_282_ = v___x_236_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_234_);
v___x_282_ = v_reuseFailAlloc_292_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_282_);
v___x_284_ = v___x_231_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_291_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_284_);
v___x_286_ = v___x_227_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_fst_225_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_290_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_286_);
lean_ctor_set(v___x_221_, 0, v___x_238_);
v___x_288_ = v___x_221_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_238_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(lean_object* v_str2_300_, lean_object* v___x_301_, lean_object* v_str1_302_, lean_object* v_cutoff_303_, lean_object* v___x_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_300_, v___x_301_, v_str1_302_, v_cutoff_303_, v___x_304_, v_a_305_);
lean_dec(v___x_304_);
lean_dec(v_cutoff_303_);
lean_dec_ref(v_str1_302_);
lean_dec(v___x_301_);
lean_dec_ref(v_str2_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* v_str1_307_, lean_object* v_str2_308_, lean_object* v_cutoff_309_){
_start:
{
lean_object* v_len1_310_; lean_object* v_len2_311_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_337_; uint8_t v___x_339_; 
v_len1_310_ = lean_string_length(v_str1_307_);
v_len2_311_ = lean_string_length(v_str2_308_);
v___x_339_ = lean_nat_dec_le(v_len1_310_, v_len2_311_);
if (v___x_339_ == 0)
{
v___y_337_ = v_len1_310_;
goto v___jp_336_;
}
else
{
v___y_337_ = v_len2_311_;
goto v___jp_336_;
}
v___jp_312_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_nat_sub(v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec(v___y_313_);
v___x_316_ = lean_nat_dec_lt(v_cutoff_309_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_i_319_; lean_object* v_v1_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_fst_329_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_len2_311_, v___x_317_);
v_i_319_ = lean_unsigned_to_nat(0u);
lean_inc_n(v___x_318_, 2);
v_v1_320_ = lean_mk_array(v___x_318_, v_i_319_);
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v_i_319_);
lean_ctor_set(v___x_321_, 1, v___x_318_);
lean_ctor_set(v___x_321_, 2, v___x_317_);
lean_inc_ref(v_v1_320_);
v___x_322_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_321_, v_v1_320_, v_i_319_);
lean_dec_ref_known(v___x_321_, 3);
v___x_323_ = lean_box(0);
v___x_324_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0));
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_v1_320_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_322_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_308_, v___x_318_, v_str1_307_, v_cutoff_309_, v___x_315_, v___x_327_);
lean_dec(v___x_315_);
lean_dec(v___x_318_);
v_fst_329_ = lean_ctor_get(v___x_328_, 0);
if (lean_obj_tag(v_fst_329_) == 0)
{
lean_object* v_snd_330_; lean_object* v_fst_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_snd_330_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_snd_330_);
lean_dec_ref(v___x_328_);
v_fst_331_ = lean_ctor_get(v_snd_330_, 0);
lean_inc(v_fst_331_);
lean_dec(v_snd_330_);
v___x_332_ = lean_array_fget(v_fst_331_, v_len2_311_);
lean_dec(v_fst_331_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
else
{
lean_object* v_val_334_; 
lean_inc_ref(v_fst_329_);
lean_dec_ref(v___x_328_);
v_val_334_ = lean_ctor_get(v_fst_329_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v_fst_329_, 1);
return v_val_334_;
}
}
else
{
lean_object* v___x_335_; 
lean_dec(v___x_315_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
}
v___jp_336_:
{
uint8_t v___x_338_; 
v___x_338_ = lean_nat_dec_le(v_len1_310_, v_len2_311_);
if (v___x_338_ == 0)
{
v___y_313_ = v___y_337_;
v___y_314_ = v_len2_311_;
goto v___jp_312_;
}
else
{
v___y_313_ = v___y_337_;
v___y_314_ = v_len1_310_;
goto v___jp_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* v_str1_340_, lean_object* v_str2_341_, lean_object* v_cutoff_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_EditDistance_levenshtein(v_str1_340_, v_str2_341_, v_cutoff_342_);
lean_dec(v_cutoff_342_);
lean_dec_ref(v_str2_341_);
lean_dec_ref(v_str1_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* v___x_344_, lean_object* v_range_345_, lean_object* v_b_346_, lean_object* v_i_347_, lean_object* v_hs_348_, lean_object* v_hl_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_345_, v_b_346_, v_i_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* v___x_351_, lean_object* v_range_352_, lean_object* v_b_353_, lean_object* v_i_354_, lean_object* v_hs_355_, lean_object* v_hl_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_351_, v_range_352_, v_b_353_, v_i_354_, v_hs_355_, v_hl_356_);
lean_dec_ref(v_range_352_);
lean_dec(v___x_351_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* v_str2_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_str1_362_, lean_object* v_inst_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_358_, v___x_359_, v___x_360_, v___x_361_, v_str1_362_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* v_str2_366_, lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v___x_369_, lean_object* v_str1_370_, lean_object* v_inst_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__1(v_str2_366_, v___x_367_, v___x_368_, v___x_369_, v_str1_370_, v_inst_371_, v_a_372_);
lean_dec_ref(v_str1_370_);
lean_dec(v___x_369_);
lean_dec_ref(v___x_368_);
lean_dec(v___x_367_);
lean_dec_ref(v_str2_366_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* v_str2_374_, lean_object* v___x_375_, lean_object* v_str1_376_, lean_object* v_cutoff_377_, lean_object* v___x_378_, lean_object* v_inst_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_374_, v___x_375_, v_str1_376_, v_cutoff_377_, v___x_378_, v_a_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* v_str2_382_, lean_object* v___x_383_, lean_object* v_str1_384_, lean_object* v_cutoff_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3(v_str2_382_, v___x_383_, v_str1_384_, v_cutoff_385_, v___x_386_, v_inst_387_, v_a_388_);
lean_dec(v___x_386_);
lean_dec(v_cutoff_385_);
lean_dec_ref(v_str1_384_);
lean_dec(v___x_383_);
lean_dec_ref(v_str2_382_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* v_str1_390_, lean_object* v___x_391_, lean_object* v_str2_392_, lean_object* v_cutoff_393_, lean_object* v___x_394_, lean_object* v_inst_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_390_, v___x_391_, v_str2_392_, v_cutoff_393_, v___x_394_, v_a_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* v_str1_398_, lean_object* v___x_399_, lean_object* v_str2_400_, lean_object* v_cutoff_401_, lean_object* v___x_402_, lean_object* v_inst_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_398_, v___x_399_, v_str2_400_, v_cutoff_401_, v___x_402_, v_inst_403_, v_a_404_);
lean_dec(v___x_402_);
lean_dec(v_cutoff_401_);
lean_dec_ref(v_str2_400_);
lean_dec(v___x_399_);
lean_dec_ref(v_str1_398_);
return v_res_405_;
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
