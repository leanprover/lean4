// Lean compiler output
// Module: Lean.Server.FileWorker.ExampleHover
// Imports: public import Lean.Elab.Do
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-- "};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value),((lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value)}};
static const lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "```"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "output"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(lean_object* v_upperBound_1_, lean_object* v_line_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_a_3_, v_upperBound_1_);
if (v___x_5_ == 0)
{
lean_dec(v_a_3_);
lean_dec_ref(v_line_2_);
return v_b_4_;
}
else
{
lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_30_; 
v_snd_6_ = lean_ctor_get(v_b_4_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_b_4_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v_b_4_, 0);
lean_dec(v_unused_31_);
v___x_8_ = v_b_4_;
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_dec(v_b_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v_decide_11_; 
v___x_10_ = lean_string_utf8_byte_size(v_line_2_);
v_decide_11_ = lean_nat_dec_eq(v_snd_6_, v___x_10_);
if (v_decide_11_ == 0)
{
uint32_t v___x_12_; lean_object* v___x_13_; uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_12_ = 32;
v___x_13_ = lean_box(0);
v___x_14_ = lean_string_utf8_get_fast(v_line_2_, v_snd_6_);
v___x_15_ = lean_uint32_dec_eq(v___x_14_, v___x_12_);
if (v___x_15_ == 0)
{
lean_object* v___x_17_; 
lean_dec(v_a_3_);
lean_dec_ref(v_line_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_13_);
v___x_17_ = v___x_8_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_snd_6_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
else
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_string_utf8_next_fast(v_line_2_, v_snd_6_);
lean_dec(v_snd_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_19_);
lean_ctor_set(v___x_8_, 0, v___x_13_);
v___x_21_ = v___x_8_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_25_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_add(v_a_3_, v___x_22_);
lean_dec(v_a_3_);
v_a_3_ = v___x_23_;
v_b_4_ = v___x_21_;
goto _start;
}
}
}
else
{
lean_object* v___x_26_; lean_object* v___x_28_; 
lean_dec(v_a_3_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v_line_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_26_);
v___x_28_ = v___x_8_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_snd_6_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg___boxed(lean_object* v_upperBound_32_, lean_object* v_line_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_32_, v_line_33_, v_a_34_, v_b_35_);
lean_dec(v_upperBound_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_zero_39_; uint8_t v_isZero_40_; 
v_zero_39_ = lean_unsigned_to_nat(0u);
v_isZero_40_ = lean_nat_dec_eq(v_x_37_, v_zero_39_);
if (v_isZero_40_ == 1)
{
lean_dec(v_x_37_);
return v_x_38_;
}
else
{
uint32_t v___x_41_; lean_object* v_one_42_; lean_object* v_n_43_; lean_object* v___x_44_; 
v___x_41_ = 32;
v_one_42_ = lean_unsigned_to_nat(1u);
v_n_43_ = lean_nat_sub(v_x_37_, v_one_42_);
lean_dec(v_x_37_);
v___x_44_ = lean_string_push(v_x_38_, v___x_41_);
v_x_37_ = v_n_43_;
v_x_38_ = v___x_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(lean_object* v_s_46_, lean_object* v_pos_47_){
_start:
{
lean_object* v_str_48_; lean_object* v_startInclusive_49_; lean_object* v_endExclusive_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v_decide_54_; 
v_str_48_ = lean_ctor_get(v_s_46_, 0);
v_startInclusive_49_ = lean_ctor_get(v_s_46_, 1);
v_endExclusive_50_ = lean_ctor_get(v_s_46_, 2);
v___x_51_ = lean_nat_add(v_startInclusive_49_, v_pos_47_);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_nat_sub(v_endExclusive_50_, v___x_51_);
v_decide_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
lean_dec(v___x_53_);
if (v_decide_54_ == 0)
{
uint32_t v___x_55_; uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_55_ = 32;
v___x_56_ = lean_string_utf8_get_fast(v_str_48_, v___x_51_);
v___x_57_ = lean_uint32_dec_eq(v___x_56_, v___x_55_);
if (v___x_57_ == 0)
{
lean_dec(v___x_51_);
return v_pos_47_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_58_ = lean_string_utf8_next_fast(v_str_48_, v___x_51_);
v___x_59_ = lean_nat_sub(v___x_58_, v___x_51_);
lean_dec(v___x_51_);
v___x_60_ = lean_nat_add(v_pos_47_, v___x_59_);
lean_dec(v___x_59_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_pos_47_, v___x_61_);
v___x_63_ = lean_nat_dec_le(v___x_62_, v___x_60_);
lean_dec(v___x_62_);
if (v___x_63_ == 0)
{
lean_dec(v___x_60_);
return v_pos_47_;
}
else
{
lean_dec(v_pos_47_);
v_pos_47_ = v___x_60_;
goto _start;
}
}
}
else
{
lean_dec(v___x_51_);
return v_pos_47_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1___boxed(lean_object* v_s_65_, lean_object* v_pos_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v_s_65_, v_pos_66_);
lean_dec_ref(v_s_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(lean_object* v_indent_73_, lean_object* v_line_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_iter_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_fst_80_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0));
lean_inc(v_indent_73_);
v___x_76_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(v_indent_73_, v___x_75_);
v_iter_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1));
lean_inc_ref(v_line_74_);
v___x_79_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_indent_73_, v_line_74_, v_iter_77_, v___x_78_);
lean_dec(v_indent_73_);
v_fst_80_ = lean_ctor_get(v___x_79_, 0);
if (lean_obj_tag(v_fst_80_) == 0)
{
lean_object* v_snd_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v_decide_86_; 
v_snd_81_ = lean_ctor_get(v___x_79_, 1);
lean_inc_n(v_snd_81_, 2);
lean_dec_ref(v___x_79_);
v___x_82_ = lean_string_utf8_byte_size(v_line_74_);
lean_inc_ref(v_line_74_);
v___x_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_83_, 0, v_line_74_);
lean_ctor_set(v___x_83_, 1, v_snd_81_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
v___x_84_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v___x_83_, v_iter_77_);
lean_dec_ref_known(v___x_83_, 3);
v___x_85_ = lean_nat_sub(v___x_82_, v_snd_81_);
v_decide_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
lean_dec(v___x_85_);
lean_dec(v___x_84_);
if (v_decide_86_ == 0)
{
lean_object* v___x_87_; lean_object* v_s_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2));
v_s_88_ = lean_string_append(v___x_76_, v___x_87_);
v___x_89_ = lean_string_utf8_extract_fast(v_line_74_, v_snd_81_, v___x_82_);
lean_dec(v_snd_81_);
lean_dec_ref(v_line_74_);
v___x_90_ = lean_string_append(v_s_88_, v___x_89_);
lean_dec_ref(v___x_89_);
return v___x_90_;
}
else
{
lean_dec(v_snd_81_);
lean_dec_ref(v___x_76_);
return v_line_74_;
}
}
else
{
lean_object* v_val_91_; 
lean_inc_ref(v_fst_80_);
lean_dec_ref(v___x_79_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v_line_74_);
v_val_91_ = lean_ctor_get(v_fst_80_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v_fst_80_, 1);
return v_val_91_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(lean_object* v_upperBound_92_, lean_object* v_line_93_, lean_object* v_inst_94_, lean_object* v_R_95_, lean_object* v_a_96_, lean_object* v_b_97_, lean_object* v_c_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_92_, v_line_93_, v_a_96_, v_b_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___boxed(lean_object* v_upperBound_100_, lean_object* v_line_101_, lean_object* v_inst_102_, lean_object* v_R_103_, lean_object* v_a_104_, lean_object* v_b_105_, lean_object* v_c_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(v_upperBound_100_, v_line_101_, v_inst_102_, v_R_103_, v_a_104_, v_b_105_, v_c_106_);
lean_dec(v_upperBound_100_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(lean_object* v_s_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_snd_110_; lean_object* v_fst_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_149_; 
v_snd_110_ = lean_ctor_get(v_a_109_, 1);
v_fst_111_ = lean_ctor_get(v_a_109_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_149_ == 0)
{
v___x_113_ = v_a_109_;
v_isShared_114_ = v_isSharedCheck_149_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_110_);
lean_inc(v_fst_111_);
lean_dec(v_a_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_149_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_148_; 
v_fst_115_ = lean_ctor_get(v_snd_110_, 0);
v_snd_116_ = lean_ctor_get(v_snd_110_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_snd_110_);
if (v_isSharedCheck_148_ == 0)
{
v___x_118_ = v_snd_110_;
v_isShared_119_ = v_isSharedCheck_148_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_snd_110_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_148_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; uint8_t v_decide_121_; 
v___x_120_ = lean_string_utf8_byte_size(v_s_108_);
v_decide_121_ = lean_nat_dec_eq(v_snd_116_, v___x_120_);
if (v_decide_121_ == 0)
{
uint32_t v___x_122_; lean_object* v___x_123_; uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_122_ = lean_string_utf8_get_fast(v_s_108_, v_snd_116_);
v___x_123_ = lean_string_utf8_next_fast(v_s_108_, v_snd_116_);
lean_dec(v_snd_116_);
v___x_124_ = 10;
v___x_125_ = lean_uint32_dec_eq(v___x_122_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_127_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_123_);
v___x_127_ = v___x_118_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_123_);
v___x_127_ = v_reuseFailAlloc_132_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_127_);
v___x_129_ = v___x_113_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
v_a_109_ = v___x_129_;
goto _start;
}
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_string_utf8_extract_fast(v_s_108_, v_fst_115_, v___x_123_);
lean_dec(v_fst_115_);
v___x_134_ = lean_array_push(v_fst_111_, v___x_133_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_123_);
lean_ctor_set(v___x_118_, 0, v___x_123_);
v___x_136_ = v___x_118_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_123_);
v___x_136_ = v_reuseFailAlloc_141_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_136_);
lean_ctor_set(v___x_113_, 0, v___x_134_);
v___x_138_ = v___x_113_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_140_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v_a_109_ = v___x_138_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_143_; 
if (v_isShared_119_ == 0)
{
v___x_143_ = v___x_118_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_snd_116_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_143_);
v___x_145_ = v___x_113_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_111_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg___boxed(lean_object* v_s_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_150_, v_a_151_);
lean_dec_ref(v_s_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(lean_object* v_s_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_snd_163_; lean_object* v_fst_164_; lean_object* v_fst_165_; lean_object* v_snd_166_; uint8_t v_decide_167_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2));
v___x_162_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_160_, v___x_161_);
v_snd_163_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_snd_163_);
v_fst_164_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_164_);
lean_dec_ref(v___x_162_);
v_fst_165_ = lean_ctor_get(v_snd_163_, 0);
lean_inc(v_fst_165_);
v_snd_166_ = lean_ctor_get(v_snd_163_, 1);
lean_inc(v_snd_166_);
lean_dec(v_snd_163_);
v_decide_167_ = lean_nat_dec_eq(v_snd_166_, v_fst_165_);
if (v_decide_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_string_utf8_extract_fast(v_s_160_, v_fst_165_, v_snd_166_);
lean_dec(v_snd_166_);
lean_dec(v_fst_165_);
v___x_169_ = lean_array_push(v_fst_164_, v___x_168_);
return v___x_169_;
}
else
{
lean_dec(v_snd_166_);
lean_dec(v_fst_165_);
return v_fst_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___boxed(lean_object* v_s_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(v_s_170_);
lean_dec_ref(v_s_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(lean_object* v_s_172_, lean_object* v_inst_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_172_, v_a_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___boxed(lean_object* v_s_176_, lean_object* v_inst_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(v_s_176_, v_inst_177_, v_a_178_);
lean_dec_ref(v_s_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl(lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_tag_nat(v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl___boxed(lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl(v_x_182_);
lean_dec(v_x_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(lean_object* v_t_184_, lean_object* v_k_185_){
_start:
{
switch(lean_obj_tag(v_t_184_))
{
case 0:
{
return v_k_185_;
}
case 1:
{
lean_object* v_ticks_186_; lean_object* v___x_187_; 
v_ticks_186_ = lean_ctor_get(v_t_184_, 0);
lean_inc(v_ticks_186_);
lean_dec_ref_known(v_t_184_, 1);
v___x_187_ = lean_apply_1(v_k_185_, v_ticks_186_);
return v___x_187_;
}
default: 
{
lean_object* v_indent_188_; lean_object* v_ticks_189_; lean_object* v___x_190_; 
v_indent_188_ = lean_ctor_get(v_t_184_, 0);
lean_inc(v_indent_188_);
v_ticks_189_ = lean_ctor_get(v_t_184_, 1);
lean_inc(v_ticks_189_);
lean_dec_ref_known(v_t_184_, 2);
v___x_190_ = lean_apply_2(v_k_185_, v_indent_188_, v_ticks_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_193_, v_k_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___boxed(lean_object* v_motive_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(v_motive_197_, v_ctorIdx_198_, v_t_199_, v_h_200_, v_k_201_);
lean_dec(v_ctorIdx_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim___redArg(lean_object* v_t_203_, lean_object* v_normal_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_203_, v_normal_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_normal_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_207_, v_normal_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim___redArg(lean_object* v_t_211_, lean_object* v_nonOutput_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_211_, v_nonOutput_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_nonOutput_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_215_, v_nonOutput_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim___redArg(lean_object* v_t_219_, lean_object* v_output_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_219_, v_output_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_output_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_223_, v_output_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(lean_object* v_s_227_, lean_object* v_pos_228_){
_start:
{
lean_object* v_str_229_; lean_object* v_startInclusive_230_; lean_object* v_endExclusive_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v_decide_235_; 
v_str_229_ = lean_ctor_get(v_s_227_, 0);
v_startInclusive_230_ = lean_ctor_get(v_s_227_, 1);
v_endExclusive_231_ = lean_ctor_get(v_s_227_, 2);
v___x_232_ = lean_nat_add(v_startInclusive_230_, v_pos_228_);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_nat_sub(v_endExclusive_231_, v___x_232_);
v_decide_235_ = lean_nat_dec_eq(v___x_233_, v___x_234_);
lean_dec(v___x_234_);
if (v_decide_235_ == 0)
{
uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_string_utf8_get_fast(v_str_229_, v___x_232_);
v___x_237_ = 96;
v___x_238_ = lean_uint32_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v___x_232_);
return v_pos_228_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_239_ = lean_string_utf8_next_fast(v_str_229_, v___x_232_);
v___x_240_ = lean_nat_sub(v___x_239_, v___x_232_);
lean_dec(v___x_232_);
v___x_241_ = lean_nat_add(v_pos_228_, v___x_240_);
lean_dec(v___x_240_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_pos_228_, v___x_242_);
v___x_244_ = lean_nat_dec_le(v___x_243_, v___x_241_);
lean_dec(v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v___x_241_);
return v_pos_228_;
}
else
{
lean_dec(v_pos_228_);
v_pos_228_ = v___x_241_;
goto _start;
}
}
}
else
{
lean_dec(v___x_232_);
return v_pos_228_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2___boxed(lean_object* v_s_246_, lean_object* v_pos_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(v_s_246_, v_pos_247_);
lean_dec_ref(v_s_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(lean_object* v_s_249_, lean_object* v_pos_250_){
_start:
{
lean_object* v_str_251_; lean_object* v_startInclusive_252_; lean_object* v_endExclusive_253_; lean_object* v___x_254_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v_decide_265_; 
v_str_251_ = lean_ctor_get(v_s_249_, 0);
v_startInclusive_252_ = lean_ctor_get(v_s_249_, 1);
v_endExclusive_253_ = lean_ctor_get(v_s_249_, 2);
v___x_254_ = lean_nat_add(v_startInclusive_252_, v_pos_250_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_nat_sub(v_endExclusive_253_, v___x_254_);
v_decide_265_ = lean_nat_dec_eq(v___x_263_, v___x_264_);
lean_dec(v___x_264_);
if (v_decide_265_ == 0)
{
uint32_t v___x_266_; uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_string_utf8_get_fast(v_str_251_, v___x_254_);
v___x_267_ = 32;
v___x_268_ = lean_uint32_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 9;
v___x_270_ = lean_uint32_dec_eq(v___x_266_, v___x_269_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 13;
v___x_272_ = lean_uint32_dec_eq(v___x_266_, v___x_271_);
if (v___x_272_ == 0)
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 10;
v___x_274_ = lean_uint32_dec_eq(v___x_266_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v___x_254_);
return v_pos_250_;
}
else
{
goto v___jp_255_;
}
}
else
{
goto v___jp_255_;
}
}
else
{
goto v___jp_255_;
}
}
else
{
goto v___jp_255_;
}
}
else
{
lean_dec(v___x_254_);
return v_pos_250_;
}
v___jp_255_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_256_ = lean_string_utf8_next_fast(v_str_251_, v___x_254_);
v___x_257_ = lean_nat_sub(v___x_256_, v___x_254_);
lean_dec(v___x_254_);
v___x_258_ = lean_nat_add(v_pos_250_, v___x_257_);
lean_dec(v___x_257_);
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_pos_250_, v___x_259_);
v___x_261_ = lean_nat_dec_le(v___x_260_, v___x_258_);
lean_dec(v___x_260_);
if (v___x_261_ == 0)
{
lean_dec(v___x_258_);
return v_pos_250_;
}
else
{
lean_dec(v_pos_250_);
v_pos_250_ = v___x_258_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0___boxed(lean_object* v_s_275_, lean_object* v_pos_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(v_s_275_, v_pos_276_);
lean_dec_ref(v_s_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(lean_object* v_s_278_, lean_object* v_pos_279_){
_start:
{
lean_object* v_str_280_; lean_object* v_startInclusive_281_; lean_object* v_endExclusive_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v_decide_286_; 
v_str_280_ = lean_ctor_get(v_s_278_, 0);
v_startInclusive_281_ = lean_ctor_get(v_s_278_, 1);
v_endExclusive_282_ = lean_ctor_get(v_s_278_, 2);
v___x_283_ = lean_nat_add(v_startInclusive_281_, v_pos_279_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_sub(v_endExclusive_282_, v___x_283_);
v_decide_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
lean_dec(v___x_285_);
if (v_decide_286_ == 0)
{
uint32_t v___x_287_; uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_string_utf8_get_fast(v_str_280_, v___x_283_);
v___x_288_ = 32;
v___x_289_ = lean_uint32_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec(v___x_283_);
return v_pos_279_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_290_ = lean_string_utf8_next_fast(v_str_280_, v___x_283_);
v___x_291_ = lean_nat_sub(v___x_290_, v___x_283_);
lean_dec(v___x_283_);
v___x_292_ = lean_nat_add(v_pos_279_, v___x_291_);
lean_dec(v___x_291_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_pos_279_, v___x_293_);
v___x_295_ = lean_nat_dec_le(v___x_294_, v___x_292_);
lean_dec(v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v___x_292_);
return v_pos_279_;
}
else
{
lean_dec(v_pos_279_);
v_pos_279_ = v___x_292_;
goto _start;
}
}
}
else
{
lean_dec(v___x_283_);
return v_pos_279_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1___boxed(lean_object* v_s_297_, lean_object* v_pos_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v_s_297_, v_pos_298_);
lean_dec_ref(v_s_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(lean_object* v_as_302_, size_t v_sz_303_, size_t v_i_304_, lean_object* v_b_305_){
_start:
{
lean_object* v_a_307_; uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_lt(v_i_304_, v_sz_303_);
if (v___x_311_ == 0)
{
return v_b_305_;
}
else
{
lean_object* v_fst_312_; lean_object* v_snd_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_381_; 
v_fst_312_ = lean_ctor_get(v_b_305_, 0);
v_snd_313_ = lean_ctor_get(v_b_305_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_b_305_);
if (v_isSharedCheck_381_ == 0)
{
v___x_315_ = v_b_305_;
v_isShared_316_ = v_isSharedCheck_381_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_313_);
lean_inc(v_fst_312_);
lean_dec(v_b_305_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_381_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_a_317_; lean_object* v_inOutput_330_; lean_object* v_inOutput_334_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_a_317_ = lean_array_uget_borrowed(v_as_302_, v_i_304_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_string_utf8_byte_size(v_a_317_);
lean_inc(v_a_317_);
v___x_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_339_, 0, v_a_317_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___x_340_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(v___x_339_, v___x_337_);
v___x_341_ = lean_unsigned_to_nat(3u);
v___x_342_ = lean_nat_sub(v___x_338_, v___x_340_);
v___x_343_ = lean_nat_dec_le(v___x_341_, v___x_342_);
lean_dec(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec(v___x_340_);
lean_dec_ref_known(v___x_339_, 3);
goto v___jp_318_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0));
v___x_345_ = lean_string_memcmp(v_a_317_, v___x_344_, v___x_340_, v___x_337_, v___x_341_);
if (v___x_345_ == 0)
{
lean_dec(v___x_340_);
lean_dec_ref_known(v___x_339_, 3);
goto v___jp_318_;
}
else
{
lean_object* v_inOutput_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_del_object(v___x_315_);
v_inOutput_346_ = lean_box(0);
v___x_347_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_339_, v___x_337_);
lean_dec_ref_known(v___x_339_, 3);
lean_inc(v___x_340_);
lean_inc(v_a_317_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v_a_317_);
lean_ctor_set(v___x_348_, 1, v___x_340_);
lean_ctor_set(v___x_348_, 2, v___x_338_);
v___x_349_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(v___x_348_, v___x_337_);
lean_dec_ref_known(v___x_348_, 3);
v___x_350_ = lean_nat_add(v___x_340_, v___x_349_);
lean_dec(v___x_349_);
v___x_351_ = lean_nat_sub(v___x_350_, v___x_340_);
lean_dec(v___x_340_);
switch(lean_obj_tag(v_snd_313_))
{
case 0:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_inc(v___x_350_);
lean_inc(v_a_317_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_317_);
lean_ctor_set(v___x_354_, 1, v___x_350_);
lean_ctor_set(v___x_354_, 2, v___x_338_);
v___x_355_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_354_, v___x_337_);
lean_dec_ref_known(v___x_354_, 3);
v___x_356_ = lean_nat_add(v___x_350_, v___x_355_);
lean_dec(v___x_355_);
lean_dec(v___x_350_);
v___x_357_ = lean_unsigned_to_nat(6u);
v___x_358_ = lean_nat_sub(v___x_338_, v___x_356_);
v___x_359_ = lean_nat_dec_le(v___x_357_, v___x_358_);
lean_dec(v___x_358_);
if (v___x_359_ == 0)
{
lean_dec(v___x_356_);
lean_dec(v___x_347_);
goto v___jp_352_;
}
else
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1));
v___x_361_ = lean_string_memcmp(v_a_317_, v___x_360_, v___x_356_, v___x_337_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_361_ == 0)
{
lean_dec(v___x_347_);
goto v___jp_352_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_347_);
lean_ctor_set(v___x_362_, 1, v___x_351_);
v_inOutput_330_ = v___x_362_;
goto v___jp_329_;
}
}
}
case 1:
{
lean_object* v_ticks_363_; uint8_t v___x_364_; 
lean_dec(v___x_350_);
lean_dec(v___x_347_);
v_ticks_363_ = lean_ctor_get(v_snd_313_, 0);
v___x_364_ = lean_nat_dec_eq(v_ticks_363_, v___x_351_);
lean_dec(v___x_351_);
if (v___x_364_ == 0)
{
v_inOutput_334_ = v_snd_313_;
goto v___jp_333_;
}
else
{
lean_dec_ref_known(v_snd_313_, 1);
v_inOutput_334_ = v_inOutput_346_;
goto v___jp_333_;
}
}
default: 
{
lean_object* v_indent_365_; lean_object* v_ticks_366_; uint8_t v___x_367_; 
lean_dec(v___x_350_);
lean_dec(v___x_347_);
v_indent_365_ = lean_ctor_get(v_snd_313_, 0);
v_ticks_366_ = lean_ctor_get(v_snd_313_, 1);
v___x_367_ = lean_nat_dec_eq(v_ticks_366_, v___x_351_);
lean_dec(v___x_351_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
lean_inc(v_a_317_);
lean_inc(v_indent_365_);
v___x_368_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_365_, v_a_317_);
v___x_369_ = lean_string_append(v_fst_312_, v___x_368_);
lean_dec_ref(v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_snd_313_);
v_a_307_ = v___x_370_;
goto v___jp_306_;
}
else
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_isSharedCheck_378_ = !lean_is_exclusive(v_snd_313_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_379_ = lean_ctor_get(v_snd_313_, 1);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_snd_313_, 0);
lean_dec(v_unused_380_);
v___x_372_ = v_snd_313_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_dec(v_snd_313_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_string_append(v_fst_312_, v_a_317_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 0);
lean_ctor_set(v___x_372_, 1, v_inOutput_346_);
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_inOutput_346_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_a_307_ = v___x_376_;
goto v___jp_306_;
}
}
}
}
}
v___jp_352_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
v_inOutput_330_ = v___x_353_;
goto v___jp_329_;
}
}
}
v___jp_318_:
{
if (lean_obj_tag(v_snd_313_) == 2)
{
lean_object* v_indent_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v_indent_319_ = lean_ctor_get(v_snd_313_, 0);
lean_inc(v_a_317_);
lean_inc(v_indent_319_);
v___x_320_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_319_, v_a_317_);
v___x_321_ = lean_string_append(v_fst_312_, v___x_320_);
lean_dec_ref(v___x_320_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_321_);
v___x_323_ = v___x_315_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_snd_313_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v_a_307_ = v___x_323_;
goto v___jp_306_;
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_string_append(v_fst_312_, v_a_317_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_325_);
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_snd_313_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_a_307_ = v___x_327_;
goto v___jp_306_;
}
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_string_append(v_fst_312_, v_a_317_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_inOutput_330_);
v_a_307_ = v___x_332_;
goto v___jp_306_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_string_append(v_fst_312_, v_a_317_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_inOutput_334_);
v_a_307_ = v___x_336_;
goto v___jp_306_;
}
}
}
v___jp_306_:
{
size_t v___x_308_; size_t v___x_309_; 
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_add(v_i_304_, v___x_308_);
v_i_304_ = v___x_309_;
v_b_305_ = v_a_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___boxed(lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_387_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_as_382_, v_sz_boxed_386_, v_i_boxed_387_, v_b_385_);
lean_dec_ref(v_as_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples(lean_object* v_docstring_392_){
_start:
{
lean_object* v_lines_393_; lean_object* v___x_394_; size_t v_sz_395_; size_t v___x_396_; lean_object* v___x_397_; lean_object* v_fst_398_; 
v_lines_393_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(v_docstring_392_);
v___x_394_ = ((lean_object*)(l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0));
v_sz_395_ = lean_array_size(v_lines_393_);
v___x_396_ = ((size_t)0ULL);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_lines_393_, v_sz_395_, v___x_396_, v___x_394_);
lean_dec_ref(v_lines_393_);
v_fst_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_fst_398_);
lean_dec_ref(v___x_397_);
return v_fst_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples___boxed(lean_object* v_docstring_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Server_FileWorker_Hover_rewriteExamples(v_docstring_399_);
lean_dec_ref(v_docstring_399_);
return v_res_400_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_ExampleHover(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_ExampleHover(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_ExampleHover(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_ExampleHover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_ExampleHover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_ExampleHover(builtin);
}
#ifdef __cplusplus
}
#endif
