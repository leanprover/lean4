// Lean compiler output
// Module: Lean.Data.Markdown.Lines
// Imports: public import Init.Data.String.Subslice public import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.While public import Init.Data.String.FindPos
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLineEnding_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_trimTrailing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_trimTrailing___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_copy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_copy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_text(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_text___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_span___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_span(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_span___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_le(v_a_1_, v_b_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; 
lean_dec(v_b_2_);
lean_inc(v_a_1_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_1_);
lean_ctor_set(v___x_4_, 1, v_a_1_);
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_a_1_);
lean_ctor_set(v___x_5_, 1, v_b_2_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped(lean_object* v_s_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Markdown_subsliceClamped___redArg(v_a_7_, v_b_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_subsliceClamped___boxed(lean_object* v_s_10_, lean_object* v_a_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Markdown_subsliceClamped(v_s_10_, v_a_11_, v_b_12_);
lean_dec_ref(v_s_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object* v_s_14_, lean_object* v_input_15_, lean_object* v_p_16_){
_start:
{
lean_object* v_endExclusive_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_endExclusive_17_ = lean_ctor_get(v_input_15_, 1);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_p_16_, v___x_18_);
v___x_20_ = lean_nat_dec_le(v___x_19_, v_endExclusive_17_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
else
{
lean_object* v_str_22_; lean_object* v_startInclusive_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_q_26_; uint32_t v___x_27_; uint32_t v___x_28_; uint8_t v___x_29_; 
v_str_22_ = lean_ctor_get(v_s_14_, 0);
v_startInclusive_23_ = lean_ctor_get(v_s_14_, 1);
v___x_24_ = lean_nat_add(v_startInclusive_23_, v_p_16_);
v___x_25_ = lean_string_utf8_next_fast(v_str_22_, v___x_24_);
v_q_26_ = lean_nat_sub(v___x_25_, v_startInclusive_23_);
v___x_27_ = lean_string_utf8_get_fast(v_str_22_, v___x_24_);
lean_dec(v___x_24_);
v___x_28_ = 10;
v___x_29_ = lean_uint32_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 13;
v___x_31_ = lean_uint32_dec_eq(v___x_27_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
lean_dec(v_q_26_);
v___x_32_ = lean_box(0);
return v___x_32_;
}
else
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_nat_add(v_q_26_, v___x_18_);
v___x_34_ = lean_nat_dec_le(v___x_33_, v_endExclusive_17_);
lean_dec(v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_q_26_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; uint32_t v___x_37_; uint8_t v___x_38_; 
v___x_36_ = lean_nat_add(v_startInclusive_23_, v_q_26_);
v___x_37_ = lean_string_utf8_get_fast(v_str_22_, v___x_36_);
v___x_38_ = lean_uint32_dec_eq(v___x_37_, v___x_28_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec(v___x_36_);
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v_q_26_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_q_26_);
v___x_40_ = lean_string_utf8_next_fast(v_str_22_, v___x_36_);
lean_dec(v___x_36_);
v___x_41_ = lean_nat_sub(v___x_40_, v_startInclusive_23_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
}
}
else
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v_q_26_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLineEnding_x3f___boxed(lean_object* v_s_44_, lean_object* v_input_45_, lean_object* v_p_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Markdown_parseLineEnding_x3f(v_s_44_, v_input_45_, v_p_46_);
lean_dec(v_p_46_);
lean_dec_ref(v_input_45_);
lean_dec_ref(v_s_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg(lean_object* v_text_48_, lean_object* v_s_49_, lean_object* v_p_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_startInclusive_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_startInclusive_52_ = lean_ctor_get(v_text_48_, 0);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_startInclusive_52_, v___x_53_);
v___x_55_ = lean_nat_dec_le(v___x_54_, v_a_51_);
lean_dec(v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_p_50_);
return v_a_51_;
}
else
{
lean_object* v___x_56_; 
v___x_56_ = l_String_Slice_Pos_prev_x3f(v_s_49_, v_a_51_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_dec_ref(v_p_50_);
return v_a_51_;
}
else
{
lean_object* v_val_57_; uint8_t v___x_58_; 
v_val_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = lean_nat_dec_le(v_startInclusive_52_, v_val_57_);
if (v___x_58_ == 0)
{
lean_dec(v_val_57_);
lean_dec_ref(v_p_50_);
return v_a_51_;
}
else
{
lean_object* v___x_59_; 
v___x_59_ = l_String_Slice_Pos_get_x3f(v_s_49_, v_val_57_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_dec(v_val_57_);
lean_dec_ref(v_p_50_);
return v_a_51_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_val_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v___x_59_, 1);
lean_inc_ref(v_p_50_);
v___x_61_ = lean_apply_1(v_p_50_, v_val_60_);
v___x_62_ = lean_unbox(v___x_61_);
if (v___x_62_ == 0)
{
lean_dec(v_val_57_);
lean_dec_ref(v_p_50_);
return v_a_51_;
}
else
{
lean_dec(v_a_51_);
v_a_51_ = v_val_57_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg___boxed(lean_object* v_text_64_, lean_object* v_s_65_, lean_object* v_p_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg(v_text_64_, v_s_65_, v_p_66_, v_a_67_);
lean_dec_ref(v_s_65_);
lean_dec_ref(v_text_64_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_trimTrailing(lean_object* v_s_69_, lean_object* v_text_70_, lean_object* v_p_71_){
_start:
{
lean_object* v_startInclusive_72_; lean_object* v_endExclusive_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_startInclusive_72_ = lean_ctor_get(v_text_70_, 0);
lean_inc(v_startInclusive_72_);
v_endExclusive_73_ = lean_ctor_get(v_text_70_, 1);
lean_inc(v_endExclusive_73_);
v___x_74_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg(v_text_70_, v_s_69_, v_p_71_, v_endExclusive_73_);
lean_dec_ref(v_text_70_);
v___x_75_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_72_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_trimTrailing___boxed(lean_object* v_s_76_, lean_object* v_text_77_, lean_object* v_p_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Markdown_trimTrailing(v_s_76_, v_text_77_, v_p_78_);
lean_dec_ref(v_s_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0(lean_object* v_text_80_, lean_object* v_s_81_, lean_object* v_p_82_, lean_object* v_inst_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___redArg(v_text_80_, v_s_81_, v_p_82_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0___boxed(lean_object* v_text_86_, lean_object* v_s_87_, lean_object* v_p_88_, lean_object* v_inst_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_trimTrailing_spec__0(v_text_86_, v_s_87_, v_p_88_, v_inst_89_, v_a_90_);
lean_dec_ref(v_s_87_);
lean_dec_ref(v_text_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object* v_line_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_array_push(v___x_94_, v_line_92_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton(lean_object* v_s_96_, lean_object* v_line_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Markdown_Lines_singleton___redArg(v_line_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_singleton___boxed(lean_object* v_s_99_, lean_object* v_line_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Markdown_Lines_singleton(v_s_99_, v_line_100_);
lean_dec_ref(v_s_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push___redArg(lean_object* v_lines_102_, lean_object* v_line_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_array_push(v_lines_102_, v_line_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push(lean_object* v_s_105_, lean_object* v_lines_106_, lean_object* v_line_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_array_push(v_lines_106_, v_line_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_push___boxed(lean_object* v_s_109_, lean_object* v_lines_110_, lean_object* v_line_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Markdown_Lines_push(v_s_109_, v_lines_110_, v_line_111_);
lean_dec_ref(v_s_109_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___redArg(lean_object* v_lines_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_fget_borrowed(v_lines_113_, v___x_114_);
lean_inc(v___x_115_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___redArg___boxed(lean_object* v_lines_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Markdown_Lines_first___redArg(v_lines_116_);
lean_dec_ref(v_lines_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first(lean_object* v_s_118_, lean_object* v_lines_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Markdown_Lines_first___redArg(v_lines_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_first___boxed(lean_object* v_s_121_, lean_object* v_lines_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Markdown_Lines_first(v_s_121_, v_lines_122_);
lean_dec_ref(v_lines_122_);
lean_dec_ref(v_s_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___redArg(lean_object* v_lines_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_array_get_size(v_lines_124_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_sub(v___x_125_, v___x_126_);
v___x_128_ = lean_array_fget_borrowed(v_lines_124_, v___x_127_);
lean_dec(v___x_127_);
lean_inc(v___x_128_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___redArg___boxed(lean_object* v_lines_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Markdown_Lines_last___redArg(v_lines_129_);
lean_dec_ref(v_lines_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last(lean_object* v_s_131_, lean_object* v_lines_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Markdown_Lines_last___redArg(v_lines_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_last___boxed(lean_object* v_s_134_, lean_object* v_lines_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Markdown_Lines_last(v_s_134_, v_lines_135_);
lean_dec_ref(v_lines_135_);
lean_dec_ref(v_s_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0(lean_object* v_s_137_, size_t v_sz_138_, size_t v_i_139_, lean_object* v_bs_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_141_ == 0)
{
return v_bs_140_;
}
else
{
lean_object* v_v_142_; lean_object* v_startInclusive_143_; lean_object* v_endExclusive_144_; lean_object* v_str_145_; lean_object* v_startInclusive_146_; lean_object* v___x_147_; lean_object* v_bs_x27_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v_v_142_ = lean_array_uget_borrowed(v_bs_140_, v_i_139_);
v_startInclusive_143_ = lean_ctor_get(v_v_142_, 0);
lean_inc(v_startInclusive_143_);
v_endExclusive_144_ = lean_ctor_get(v_v_142_, 1);
lean_inc(v_endExclusive_144_);
v_str_145_ = lean_ctor_get(v_s_137_, 0);
v_startInclusive_146_ = lean_ctor_get(v_s_137_, 1);
v___x_147_ = lean_unsigned_to_nat(0u);
v_bs_x27_148_ = lean_array_uset(v_bs_140_, v_i_139_, v___x_147_);
v___x_149_ = lean_nat_add(v_startInclusive_146_, v_startInclusive_143_);
lean_dec(v_startInclusive_143_);
v___x_150_ = lean_nat_add(v_startInclusive_146_, v_endExclusive_144_);
lean_dec(v_endExclusive_144_);
v___x_151_ = lean_string_utf8_extract_fast(v_str_145_, v___x_149_, v___x_150_);
lean_dec(v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_add(v_i_139_, v___x_152_);
v___x_154_ = lean_array_uset(v_bs_x27_148_, v_i_139_, v___x_151_);
v_i_139_ = v___x_153_;
v_bs_140_ = v___x_154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0___boxed(lean_object* v_s_156_, lean_object* v_sz_157_, lean_object* v_i_158_, lean_object* v_bs_159_){
_start:
{
size_t v_sz_boxed_160_; size_t v_i_boxed_161_; lean_object* v_res_162_; 
v_sz_boxed_160_ = lean_unbox_usize(v_sz_157_);
lean_dec(v_sz_157_);
v_i_boxed_161_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0(v_s_156_, v_sz_boxed_160_, v_i_boxed_161_, v_bs_159_);
lean_dec_ref(v_s_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_copy(lean_object* v_s_163_, lean_object* v_lines_164_){
_start:
{
size_t v_sz_165_; size_t v___x_166_; lean_object* v___x_167_; 
v_sz_165_ = lean_array_size(v_lines_164_);
v___x_166_ = ((size_t)0ULL);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Lines_copy_spec__0(v_s_163_, v_sz_165_, v___x_166_, v_lines_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_copy___boxed(lean_object* v_s_168_, lean_object* v_lines_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Markdown_Lines_copy(v_s_168_, v_lines_169_);
lean_dec_ref(v_s_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_text(lean_object* v_s_171_, lean_object* v_lines_172_, lean_object* v_sep_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = l_Lean_Markdown_Lines_copy(v_s_171_, v_lines_172_);
v___x_175_ = lean_array_to_list(v___x_174_);
v___x_176_ = l_String_intercalate(v_sep_173_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_text___boxed(lean_object* v_s_177_, lean_object* v_lines_178_, lean_object* v_sep_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Markdown_Lines_text(v_s_177_, v_lines_178_, v_sep_179_);
lean_dec_ref(v_sep_179_);
lean_dec_ref(v_s_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_instInhabited(lean_object* v_s_181_){
_start:
{
lean_object* v_startInclusive_182_; lean_object* v_endExclusive_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_startInclusive_182_ = lean_ctor_get(v_s_181_, 1);
v_endExclusive_183_ = lean_ctor_get(v_s_181_, 2);
v___x_184_ = lean_nat_sub(v_endExclusive_183_, v_startInclusive_182_);
lean_inc(v___x_184_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_instInhabited___boxed(lean_object* v_s_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Markdown_Lines_instInhabited(v_s_187_);
lean_dec_ref(v_s_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_span___redArg(lean_object* v_first_189_, lean_object* v_last_190_){
_start:
{
lean_object* v_startInclusive_191_; lean_object* v_endExclusive_192_; lean_object* v___x_193_; 
v_startInclusive_191_ = lean_ctor_get(v_first_189_, 0);
lean_inc(v_startInclusive_191_);
lean_dec_ref(v_first_189_);
v_endExclusive_192_ = lean_ctor_get(v_last_190_, 1);
lean_inc(v_endExclusive_192_);
lean_dec_ref(v_last_190_);
v___x_193_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_191_, v_endExclusive_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_span(lean_object* v_s_194_, lean_object* v_first_195_, lean_object* v_last_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Markdown_span___redArg(v_first_195_, v_last_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_span___boxed(lean_object* v_s_198_, lean_object* v_first_199_, lean_object* v_last_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Markdown_span(v_s_198_, v_first_199_, v_last_200_);
lean_dec_ref(v_s_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___redArg(lean_object* v_lines_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = l_Lean_Markdown_Lines_first___redArg(v_lines_202_);
v___x_204_ = l_Lean_Markdown_Lines_last___redArg(v_lines_202_);
v___x_205_ = l_Lean_Markdown_span___redArg(v___x_203_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___redArg___boxed(lean_object* v_lines_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Markdown_Lines_extent___redArg(v_lines_206_);
lean_dec_ref(v_lines_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent(lean_object* v_s_208_, lean_object* v_lines_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Markdown_Lines_extent___redArg(v_lines_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Lines_extent___boxed(lean_object* v_s_211_, lean_object* v_lines_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Markdown_Lines_extent(v_s_211_, v_lines_212_);
lean_dec_ref(v_lines_212_);
lean_dec_ref(v_s_211_);
return v_res_213_;
}
}
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Lines(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Lines(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Lines(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Lines(builtin);
}
#ifdef __cplusplus
}
#endif
