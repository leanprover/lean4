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
lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_27_; 
v_snd_6_ = lean_ctor_get(v_b_4_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_b_4_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v_b_4_, 0);
lean_dec(v_unused_28_);
v___x_8_ = v_b_4_;
v_isShared_9_ = v_isSharedCheck_27_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_dec(v_b_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_27_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_15_; uint8_t v_decide_16_; 
v___x_15_ = lean_string_utf8_byte_size(v_line_2_);
v_decide_16_ = lean_nat_dec_eq(v_snd_6_, v___x_15_);
if (v_decide_16_ == 0)
{
if (v___x_5_ == 0)
{
lean_dec(v_a_3_);
goto v___jp_10_;
}
else
{
uint32_t v___x_17_; lean_object* v___x_18_; uint32_t v___x_19_; uint8_t v___x_20_; 
lean_del_object(v___x_8_);
v___x_17_ = 32;
v___x_18_ = lean_box(0);
v___x_19_ = lean_string_utf8_get_fast(v_line_2_, v_snd_6_);
v___x_20_ = lean_uint32_dec_eq(v___x_19_, v___x_17_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v_a_3_);
lean_dec_ref(v_line_2_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_18_);
lean_ctor_set(v___x_21_, 1, v_snd_6_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = lean_string_utf8_next_fast(v_line_2_, v_snd_6_);
lean_dec(v_snd_6_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_18_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_add(v_a_3_, v___x_24_);
lean_dec(v_a_3_);
v_a_3_ = v___x_25_;
v_b_4_ = v___x_23_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3_);
goto v___jp_10_;
}
v___jp_10_:
{
lean_object* v___x_11_; lean_object* v___x_13_; 
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v_line_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_11_);
v___x_13_ = v___x_8_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_snd_6_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg___boxed(lean_object* v_upperBound_29_, lean_object* v_line_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_29_, v_line_30_, v_a_31_, v_b_32_);
lean_dec(v_upperBound_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_x_34_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_dec(v_x_34_);
return v_x_35_;
}
else
{
uint32_t v___x_38_; lean_object* v_one_39_; lean_object* v_n_40_; lean_object* v___x_41_; 
v___x_38_ = 32;
v_one_39_ = lean_unsigned_to_nat(1u);
v_n_40_ = lean_nat_sub(v_x_34_, v_one_39_);
lean_dec(v_x_34_);
v___x_41_ = lean_string_push(v_x_35_, v___x_38_);
v_x_34_ = v_n_40_;
v_x_35_ = v___x_41_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(lean_object* v_s_43_, lean_object* v_pos_44_){
_start:
{
lean_object* v_str_45_; lean_object* v_startInclusive_46_; lean_object* v_endExclusive_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v_decide_51_; 
v_str_45_ = lean_ctor_get(v_s_43_, 0);
v_startInclusive_46_ = lean_ctor_get(v_s_43_, 1);
v_endExclusive_47_ = lean_ctor_get(v_s_43_, 2);
v___x_48_ = lean_nat_add(v_startInclusive_46_, v_pos_44_);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_sub(v_endExclusive_47_, v___x_48_);
v_decide_51_ = lean_nat_dec_eq(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
if (v_decide_51_ == 0)
{
uint32_t v___x_52_; uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_52_ = 32;
v___x_53_ = lean_string_utf8_get_fast(v_str_45_, v___x_48_);
v___x_54_ = lean_uint32_dec_eq(v___x_53_, v___x_52_);
if (v___x_54_ == 0)
{
lean_dec(v___x_48_);
return v_pos_44_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_55_ = lean_string_utf8_next_fast(v_str_45_, v___x_48_);
v___x_56_ = lean_nat_sub(v___x_55_, v___x_48_);
lean_dec(v___x_48_);
v___x_57_ = lean_nat_add(v_pos_44_, v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_pos_44_, v___x_58_);
v___x_60_ = lean_nat_dec_le(v___x_59_, v___x_57_);
lean_dec(v___x_59_);
if (v___x_60_ == 0)
{
lean_dec(v___x_57_);
return v_pos_44_;
}
else
{
lean_dec(v_pos_44_);
v_pos_44_ = v___x_57_;
goto _start;
}
}
}
else
{
lean_dec(v___x_48_);
return v_pos_44_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1___boxed(lean_object* v_s_62_, lean_object* v_pos_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v_s_62_, v_pos_63_);
lean_dec_ref(v_s_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(lean_object* v_indent_70_, lean_object* v_line_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_iter_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_fst_77_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0));
lean_inc(v_indent_70_);
v___x_73_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(v_indent_70_, v___x_72_);
v_iter_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1));
lean_inc_ref(v_line_71_);
v___x_76_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_indent_70_, v_line_71_, v_iter_74_, v___x_75_);
lean_dec(v_indent_70_);
v_fst_77_ = lean_ctor_get(v___x_76_, 0);
if (lean_obj_tag(v_fst_77_) == 0)
{
lean_object* v_snd_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v_decide_83_; 
v_snd_78_ = lean_ctor_get(v___x_76_, 1);
lean_inc_n(v_snd_78_, 2);
lean_dec_ref(v___x_76_);
v___x_79_ = lean_string_utf8_byte_size(v_line_71_);
lean_inc_ref(v_line_71_);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v_line_71_);
lean_ctor_set(v___x_80_, 1, v_snd_78_);
lean_ctor_set(v___x_80_, 2, v___x_79_);
v___x_81_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v___x_80_, v_iter_74_);
lean_dec_ref_known(v___x_80_, 3);
v___x_82_ = lean_nat_sub(v___x_79_, v_snd_78_);
v_decide_83_ = lean_nat_dec_eq(v___x_81_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_81_);
if (v_decide_83_ == 0)
{
lean_object* v___x_84_; lean_object* v_s_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2));
v_s_85_ = lean_string_append(v___x_73_, v___x_84_);
v___x_86_ = lean_string_utf8_extract_fast(v_line_71_, v_snd_78_, v___x_79_);
lean_dec(v_snd_78_);
lean_dec_ref(v_line_71_);
v___x_87_ = lean_string_append(v_s_85_, v___x_86_);
lean_dec_ref(v___x_86_);
return v___x_87_;
}
else
{
lean_dec(v_snd_78_);
lean_dec_ref(v___x_73_);
return v_line_71_;
}
}
else
{
lean_object* v_val_88_; 
lean_inc_ref(v_fst_77_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v_line_71_);
v_val_88_ = lean_ctor_get(v_fst_77_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v_fst_77_, 1);
return v_val_88_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(lean_object* v_upperBound_89_, lean_object* v_line_90_, lean_object* v_inst_91_, lean_object* v_R_92_, lean_object* v_a_93_, lean_object* v_b_94_, lean_object* v_c_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_89_, v_line_90_, v_a_93_, v_b_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___boxed(lean_object* v_upperBound_97_, lean_object* v_line_98_, lean_object* v_inst_99_, lean_object* v_R_100_, lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_c_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(v_upperBound_97_, v_line_98_, v_inst_99_, v_R_100_, v_a_101_, v_b_102_, v_c_103_);
lean_dec(v_upperBound_97_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(lean_object* v_s_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_snd_107_; lean_object* v_fst_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_146_; 
v_snd_107_ = lean_ctor_get(v_a_106_, 1);
v_fst_108_ = lean_ctor_get(v_a_106_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_146_ == 0)
{
v___x_110_ = v_a_106_;
v_isShared_111_ = v_isSharedCheck_146_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_snd_107_);
lean_inc(v_fst_108_);
lean_dec(v_a_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_146_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_145_; 
v_fst_112_ = lean_ctor_get(v_snd_107_, 0);
v_snd_113_ = lean_ctor_get(v_snd_107_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_snd_107_);
if (v_isSharedCheck_145_ == 0)
{
v___x_115_ = v_snd_107_;
v_isShared_116_ = v_isSharedCheck_145_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_snd_113_);
lean_inc(v_fst_112_);
lean_dec(v_snd_107_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_145_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint8_t v_decide_118_; 
v___x_117_ = lean_string_utf8_byte_size(v_s_105_);
v_decide_118_ = lean_nat_dec_eq(v_snd_113_, v___x_117_);
if (v_decide_118_ == 0)
{
uint32_t v___x_119_; lean_object* v___x_120_; uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_119_ = lean_string_utf8_get_fast(v_s_105_, v_snd_113_);
v___x_120_ = lean_string_utf8_next_fast(v_s_105_, v_snd_113_);
lean_dec(v_snd_113_);
v___x_121_ = 10;
v___x_122_ = lean_uint32_dec_eq(v___x_119_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_120_);
v___x_124_ = v___x_115_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_fst_112_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_120_);
v___x_124_ = v_reuseFailAlloc_129_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_124_);
v___x_126_ = v___x_110_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_fst_108_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_a_106_ = v___x_126_;
goto _start;
}
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_string_utf8_extract_fast(v_s_105_, v_fst_112_, v___x_120_);
lean_dec(v_fst_112_);
v___x_131_ = lean_array_push(v_fst_108_, v___x_130_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_120_);
lean_ctor_set(v___x_115_, 0, v___x_120_);
v___x_133_ = v___x_115_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_120_);
v___x_133_ = v_reuseFailAlloc_138_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_133_);
lean_ctor_set(v___x_110_, 0, v___x_131_);
v___x_135_ = v___x_110_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
v_a_106_ = v___x_135_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_140_; 
if (v_isShared_116_ == 0)
{
v___x_140_ = v___x_115_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_fst_112_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_113_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_140_);
v___x_142_ = v___x_110_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_fst_108_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg___boxed(lean_object* v_s_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_147_, v_a_148_);
lean_dec_ref(v_s_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(lean_object* v_s_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_snd_160_; lean_object* v_fst_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; uint8_t v_decide_164_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2));
v___x_159_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_157_, v___x_158_);
v_snd_160_ = lean_ctor_get(v___x_159_, 1);
lean_inc(v_snd_160_);
v_fst_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fst_161_);
lean_dec_ref(v___x_159_);
v_fst_162_ = lean_ctor_get(v_snd_160_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v_snd_160_, 1);
lean_inc(v_snd_163_);
lean_dec(v_snd_160_);
v_decide_164_ = lean_nat_dec_eq(v_snd_163_, v_fst_162_);
if (v_decide_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_string_utf8_extract_fast(v_s_157_, v_fst_162_, v_snd_163_);
lean_dec(v_snd_163_);
lean_dec(v_fst_162_);
v___x_166_ = lean_array_push(v_fst_161_, v___x_165_);
return v___x_166_;
}
else
{
lean_dec(v_snd_163_);
lean_dec(v_fst_162_);
return v_fst_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___boxed(lean_object* v_s_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(v_s_167_);
lean_dec_ref(v_s_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(lean_object* v_s_169_, lean_object* v_inst_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_169_, v_a_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___boxed(lean_object* v_s_173_, lean_object* v_inst_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(v_s_173_, v_inst_174_, v_a_175_);
lean_dec_ref(v_s_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl(lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_tag_nat(v_x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl___boxed(lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___impl(v_x_179_);
lean_dec(v_x_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(lean_object* v_t_181_, lean_object* v_k_182_){
_start:
{
switch(lean_obj_tag(v_t_181_))
{
case 0:
{
return v_k_182_;
}
case 1:
{
lean_object* v_ticks_183_; lean_object* v___x_184_; 
v_ticks_183_ = lean_ctor_get(v_t_181_, 0);
lean_inc(v_ticks_183_);
lean_dec_ref_known(v_t_181_, 1);
v___x_184_ = lean_apply_1(v_k_182_, v_ticks_183_);
return v___x_184_;
}
default: 
{
lean_object* v_indent_185_; lean_object* v_ticks_186_; lean_object* v___x_187_; 
v_indent_185_ = lean_ctor_get(v_t_181_, 0);
lean_inc(v_indent_185_);
v_ticks_186_ = lean_ctor_get(v_t_181_, 1);
lean_inc(v_ticks_186_);
lean_dec_ref_known(v_t_181_, 2);
v___x_187_ = lean_apply_2(v_k_182_, v_indent_185_, v_ticks_186_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_190_, v_k_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___boxed(lean_object* v_motive_194_, lean_object* v_ctorIdx_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_k_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(v_motive_194_, v_ctorIdx_195_, v_t_196_, v_h_197_, v_k_198_);
lean_dec(v_ctorIdx_195_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim___redArg(lean_object* v_t_200_, lean_object* v_normal_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_200_, v_normal_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim(lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_normal_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_204_, v_normal_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim___redArg(lean_object* v_t_208_, lean_object* v_nonOutput_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_208_, v_nonOutput_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_nonOutput_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_212_, v_nonOutput_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim___redArg(lean_object* v_t_216_, lean_object* v_output_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_216_, v_output_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim(lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_output_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_220_, v_output_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(lean_object* v_s_224_, lean_object* v_pos_225_){
_start:
{
lean_object* v_str_226_; lean_object* v_startInclusive_227_; lean_object* v_endExclusive_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v_decide_232_; 
v_str_226_ = lean_ctor_get(v_s_224_, 0);
v_startInclusive_227_ = lean_ctor_get(v_s_224_, 1);
v_endExclusive_228_ = lean_ctor_get(v_s_224_, 2);
v___x_229_ = lean_nat_add(v_startInclusive_227_, v_pos_225_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_nat_sub(v_endExclusive_228_, v___x_229_);
v_decide_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
lean_dec(v___x_231_);
if (v_decide_232_ == 0)
{
uint32_t v___x_233_; uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = lean_string_utf8_get_fast(v_str_226_, v___x_229_);
v___x_234_ = 96;
v___x_235_ = lean_uint32_dec_eq(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v___x_229_);
return v_pos_225_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_236_ = lean_string_utf8_next_fast(v_str_226_, v___x_229_);
v___x_237_ = lean_nat_sub(v___x_236_, v___x_229_);
lean_dec(v___x_229_);
v___x_238_ = lean_nat_add(v_pos_225_, v___x_237_);
lean_dec(v___x_237_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_pos_225_, v___x_239_);
v___x_241_ = lean_nat_dec_le(v___x_240_, v___x_238_);
lean_dec(v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v___x_238_);
return v_pos_225_;
}
else
{
lean_dec(v_pos_225_);
v_pos_225_ = v___x_238_;
goto _start;
}
}
}
else
{
lean_dec(v___x_229_);
return v_pos_225_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2___boxed(lean_object* v_s_243_, lean_object* v_pos_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(v_s_243_, v_pos_244_);
lean_dec_ref(v_s_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(lean_object* v_s_246_, lean_object* v_pos_247_){
_start:
{
lean_object* v_str_248_; lean_object* v_startInclusive_249_; lean_object* v_endExclusive_250_; lean_object* v___x_251_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v_decide_262_; 
v_str_248_ = lean_ctor_get(v_s_246_, 0);
v_startInclusive_249_ = lean_ctor_get(v_s_246_, 1);
v_endExclusive_250_ = lean_ctor_get(v_s_246_, 2);
v___x_251_ = lean_nat_add(v_startInclusive_249_, v_pos_247_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_nat_sub(v_endExclusive_250_, v___x_251_);
v_decide_262_ = lean_nat_dec_eq(v___x_260_, v___x_261_);
lean_dec(v___x_261_);
if (v_decide_262_ == 0)
{
uint32_t v___x_263_; uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_string_utf8_get_fast(v_str_248_, v___x_251_);
v___x_264_ = 32;
v___x_265_ = lean_uint32_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 9;
v___x_267_ = lean_uint32_dec_eq(v___x_263_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 13;
v___x_269_ = lean_uint32_dec_eq(v___x_263_, v___x_268_);
if (v___x_269_ == 0)
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 10;
v___x_271_ = lean_uint32_dec_eq(v___x_263_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v___x_251_);
return v_pos_247_;
}
else
{
goto v___jp_252_;
}
}
else
{
goto v___jp_252_;
}
}
else
{
goto v___jp_252_;
}
}
else
{
goto v___jp_252_;
}
}
else
{
lean_dec(v___x_251_);
return v_pos_247_;
}
v___jp_252_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_253_ = lean_string_utf8_next_fast(v_str_248_, v___x_251_);
v___x_254_ = lean_nat_sub(v___x_253_, v___x_251_);
lean_dec(v___x_251_);
v___x_255_ = lean_nat_add(v_pos_247_, v___x_254_);
lean_dec(v___x_254_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_pos_247_, v___x_256_);
v___x_258_ = lean_nat_dec_le(v___x_257_, v___x_255_);
lean_dec(v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v___x_255_);
return v_pos_247_;
}
else
{
lean_dec(v_pos_247_);
v_pos_247_ = v___x_255_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0___boxed(lean_object* v_s_272_, lean_object* v_pos_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(v_s_272_, v_pos_273_);
lean_dec_ref(v_s_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(lean_object* v_s_275_, lean_object* v_pos_276_){
_start:
{
lean_object* v_str_277_; lean_object* v_startInclusive_278_; lean_object* v_endExclusive_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v_decide_283_; 
v_str_277_ = lean_ctor_get(v_s_275_, 0);
v_startInclusive_278_ = lean_ctor_get(v_s_275_, 1);
v_endExclusive_279_ = lean_ctor_get(v_s_275_, 2);
v___x_280_ = lean_nat_add(v_startInclusive_278_, v_pos_276_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_sub(v_endExclusive_279_, v___x_280_);
v_decide_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
lean_dec(v___x_282_);
if (v_decide_283_ == 0)
{
uint32_t v___x_284_; uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_string_utf8_get_fast(v_str_277_, v___x_280_);
v___x_285_ = 32;
v___x_286_ = lean_uint32_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v___x_280_);
return v_pos_276_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_287_ = lean_string_utf8_next_fast(v_str_277_, v___x_280_);
v___x_288_ = lean_nat_sub(v___x_287_, v___x_280_);
lean_dec(v___x_280_);
v___x_289_ = lean_nat_add(v_pos_276_, v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_pos_276_, v___x_290_);
v___x_292_ = lean_nat_dec_le(v___x_291_, v___x_289_);
lean_dec(v___x_291_);
if (v___x_292_ == 0)
{
lean_dec(v___x_289_);
return v_pos_276_;
}
else
{
lean_dec(v_pos_276_);
v_pos_276_ = v___x_289_;
goto _start;
}
}
}
else
{
lean_dec(v___x_280_);
return v_pos_276_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1___boxed(lean_object* v_s_294_, lean_object* v_pos_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v_s_294_, v_pos_295_);
lean_dec_ref(v_s_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(lean_object* v_as_299_, size_t v_sz_300_, size_t v_i_301_, lean_object* v_b_302_){
_start:
{
lean_object* v_a_304_; uint8_t v___x_308_; 
v___x_308_ = lean_usize_dec_lt(v_i_301_, v_sz_300_);
if (v___x_308_ == 0)
{
return v_b_302_;
}
else
{
lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_378_; 
v_fst_309_ = lean_ctor_get(v_b_302_, 0);
v_snd_310_ = lean_ctor_get(v_b_302_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_b_302_);
if (v_isSharedCheck_378_ == 0)
{
v___x_312_ = v_b_302_;
v_isShared_313_ = v_isSharedCheck_378_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v_b_302_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_378_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_a_314_; lean_object* v_inOutput_327_; lean_object* v_inOutput_331_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_a_314_ = lean_array_uget_borrowed(v_as_299_, v_i_301_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_string_utf8_byte_size(v_a_314_);
lean_inc(v_a_314_);
v___x_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_336_, 0, v_a_314_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
v___x_337_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(v___x_336_, v___x_334_);
v___x_338_ = lean_unsigned_to_nat(3u);
v___x_339_ = lean_nat_sub(v___x_335_, v___x_337_);
v___x_340_ = lean_nat_dec_le(v___x_338_, v___x_339_);
lean_dec(v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v___x_337_);
lean_dec_ref_known(v___x_336_, 3);
goto v___jp_315_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0));
v___x_342_ = lean_string_memcmp(v_a_314_, v___x_341_, v___x_337_, v___x_334_, v___x_338_);
if (v___x_342_ == 0)
{
lean_dec(v___x_337_);
lean_dec_ref_known(v___x_336_, 3);
goto v___jp_315_;
}
else
{
lean_object* v_inOutput_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_del_object(v___x_312_);
v_inOutput_343_ = lean_box(0);
v___x_344_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_336_, v___x_334_);
lean_dec_ref_known(v___x_336_, 3);
lean_inc(v___x_337_);
lean_inc(v_a_314_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v_a_314_);
lean_ctor_set(v___x_345_, 1, v___x_337_);
lean_ctor_set(v___x_345_, 2, v___x_335_);
v___x_346_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(v___x_345_, v___x_334_);
lean_dec_ref_known(v___x_345_, 3);
v___x_347_ = lean_nat_add(v___x_337_, v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = lean_nat_sub(v___x_347_, v___x_337_);
lean_dec(v___x_337_);
switch(lean_obj_tag(v_snd_310_))
{
case 0:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
lean_inc(v___x_347_);
lean_inc(v_a_314_);
v___x_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_314_);
lean_ctor_set(v___x_351_, 1, v___x_347_);
lean_ctor_set(v___x_351_, 2, v___x_335_);
v___x_352_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_351_, v___x_334_);
lean_dec_ref_known(v___x_351_, 3);
v___x_353_ = lean_nat_add(v___x_347_, v___x_352_);
lean_dec(v___x_352_);
lean_dec(v___x_347_);
v___x_354_ = lean_unsigned_to_nat(6u);
v___x_355_ = lean_nat_sub(v___x_335_, v___x_353_);
v___x_356_ = lean_nat_dec_le(v___x_354_, v___x_355_);
lean_dec(v___x_355_);
if (v___x_356_ == 0)
{
lean_dec(v___x_353_);
lean_dec(v___x_344_);
goto v___jp_349_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1));
v___x_358_ = lean_string_memcmp(v_a_314_, v___x_357_, v___x_353_, v___x_334_, v___x_354_);
lean_dec(v___x_353_);
if (v___x_358_ == 0)
{
lean_dec(v___x_344_);
goto v___jp_349_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_344_);
lean_ctor_set(v___x_359_, 1, v___x_348_);
v_inOutput_327_ = v___x_359_;
goto v___jp_326_;
}
}
}
case 1:
{
lean_object* v_ticks_360_; uint8_t v___x_361_; 
lean_dec(v___x_347_);
lean_dec(v___x_344_);
v_ticks_360_ = lean_ctor_get(v_snd_310_, 0);
v___x_361_ = lean_nat_dec_eq(v_ticks_360_, v___x_348_);
lean_dec(v___x_348_);
if (v___x_361_ == 0)
{
v_inOutput_331_ = v_snd_310_;
goto v___jp_330_;
}
else
{
lean_dec_ref_known(v_snd_310_, 1);
v_inOutput_331_ = v_inOutput_343_;
goto v___jp_330_;
}
}
default: 
{
lean_object* v_indent_362_; lean_object* v_ticks_363_; uint8_t v___x_364_; 
lean_dec(v___x_347_);
lean_dec(v___x_344_);
v_indent_362_ = lean_ctor_get(v_snd_310_, 0);
v_ticks_363_ = lean_ctor_get(v_snd_310_, 1);
v___x_364_ = lean_nat_dec_eq(v_ticks_363_, v___x_348_);
lean_dec(v___x_348_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc(v_a_314_);
lean_inc(v_indent_362_);
v___x_365_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_362_, v_a_314_);
v___x_366_ = lean_string_append(v_fst_309_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_snd_310_);
v_a_304_ = v___x_367_;
goto v___jp_303_;
}
else
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_isSharedCheck_375_ = !lean_is_exclusive(v_snd_310_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_snd_310_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_snd_310_, 0);
lean_dec(v_unused_377_);
v___x_369_ = v_snd_310_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_snd_310_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_string_append(v_fst_309_, v_a_314_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 0);
lean_ctor_set(v___x_369_, 1, v_inOutput_343_);
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_inOutput_343_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v_a_304_ = v___x_373_;
goto v___jp_303_;
}
}
}
}
}
v___jp_349_:
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
v_inOutput_327_ = v___x_350_;
goto v___jp_326_;
}
}
}
v___jp_315_:
{
if (lean_obj_tag(v_snd_310_) == 2)
{
lean_object* v_indent_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v_indent_316_ = lean_ctor_get(v_snd_310_, 0);
lean_inc(v_a_314_);
lean_inc(v_indent_316_);
v___x_317_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_316_, v_a_314_);
v___x_318_ = lean_string_append(v_fst_309_, v___x_317_);
lean_dec_ref(v___x_317_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_318_);
v___x_320_ = v___x_312_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_snd_310_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v_a_304_ = v___x_320_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_string_append(v_fst_309_, v_a_314_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_322_);
v___x_324_ = v___x_312_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_snd_310_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v_a_304_ = v___x_324_;
goto v___jp_303_;
}
}
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_string_append(v_fst_309_, v_a_314_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_inOutput_327_);
v_a_304_ = v___x_329_;
goto v___jp_303_;
}
v___jp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_string_append(v_fst_309_, v_a_314_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_inOutput_331_);
v_a_304_ = v___x_333_;
goto v___jp_303_;
}
}
}
v___jp_303_:
{
size_t v___x_305_; size_t v___x_306_; 
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_301_, v___x_305_);
v_i_301_ = v___x_306_;
v_b_302_ = v_a_304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___boxed(lean_object* v_as_379_, lean_object* v_sz_380_, lean_object* v_i_381_, lean_object* v_b_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_380_);
lean_dec(v_sz_380_);
v_i_boxed_384_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_as_379_, v_sz_boxed_383_, v_i_boxed_384_, v_b_382_);
lean_dec_ref(v_as_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples(lean_object* v_docstring_389_){
_start:
{
lean_object* v_lines_390_; lean_object* v___x_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v_fst_395_; 
v_lines_390_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(v_docstring_389_);
v___x_391_ = ((lean_object*)(l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0));
v_sz_392_ = lean_array_size(v_lines_390_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_lines_390_, v_sz_392_, v___x_393_, v___x_391_);
lean_dec_ref(v_lines_390_);
v_fst_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_fst_395_);
lean_dec_ref(v___x_394_);
return v_fst_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples___boxed(lean_object* v_docstring_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Server_FileWorker_Hover_rewriteExamples(v_docstring_396_);
lean_dec_ref(v_docstring_396_);
return v_res_397_;
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
