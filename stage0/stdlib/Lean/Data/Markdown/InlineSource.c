// Lean compiler output
// Module: Lean.Data.Markdown.InlineSource
// Imports: public import Init.Data.Array.Basic public import Init.While import Init.Omega import Init.Data.Array.MapIdx import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Data.String.OrderInstances public import Lean.Data.Markdown.Lines
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_trimTrailing(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back(lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_linesBetween(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_linesBetween___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineSource_ofLines___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_InlineSource_ofLines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_InlineSource_ofLines___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_InlineSource_ofLines___closed__0 = (const lean_object*)&l_Lean_Markdown_InlineSource_ofLines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___redArg(lean_object* v_src_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v_startInclusive_4_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_array_fget_borrowed(v_src_1_, v___x_2_);
v_startInclusive_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_startInclusive_4_);
return v_startInclusive_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___redArg___boxed(lean_object* v_src_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Markdown_InlineSource_startPos___redArg(v_src_5_);
lean_dec_ref(v_src_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos(lean_object* v_s_7_, lean_object* v_src_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Markdown_InlineSource_startPos___redArg(v_src_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_startPos___boxed(lean_object* v_s_10_, lean_object* v_src_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Markdown_InlineSource_startPos(v_s_10_, v_src_11_);
lean_dec_ref(v_src_11_);
lean_dec_ref(v_s_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg(lean_object* v_src_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_endExclusive_18_; 
v___x_14_ = lean_array_get_size(v_src_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_17_ = lean_array_fget_borrowed(v_src_13_, v___x_16_);
lean_dec(v___x_16_);
v_endExclusive_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_endExclusive_18_);
return v_endExclusive_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg___boxed(lean_object* v_src_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Markdown_InlineSource_stopPos___redArg(v_src_19_);
lean_dec_ref(v_src_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos(lean_object* v_s_21_, lean_object* v_src_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Markdown_InlineSource_stopPos___redArg(v_src_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_stopPos___boxed(lean_object* v_s_24_, lean_object* v_src_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Markdown_InlineSource_stopPos(v_s_24_, v_src_25_);
lean_dec_ref(v_src_25_);
lean_dec_ref(v_s_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg(lean_object* v_src_27_, lean_object* v_p_28_, lean_object* v_lo_29_, lean_object* v_hi_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_lt(v_lo_29_, v_hi_30_);
if (v___x_31_ == 0)
{
lean_dec(v_hi_30_);
return v_lo_29_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_endExclusive_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_32_ = lean_nat_add(v_lo_29_, v_hi_30_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_shiftr(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_array_fget_borrowed(v_src_27_, v___x_34_);
v_endExclusive_36_ = lean_ctor_get(v___x_35_, 1);
v___x_37_ = lean_nat_add(v_p_28_, v___x_33_);
v___x_38_ = lean_nat_dec_le(v___x_37_, v_endExclusive_36_);
lean_dec(v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec(v_lo_29_);
v___x_39_ = lean_nat_add(v___x_34_, v___x_33_);
lean_dec(v___x_34_);
v_lo_29_ = v___x_39_;
goto _start;
}
else
{
lean_dec(v_hi_30_);
v_hi_30_ = v___x_34_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg___boxed(lean_object* v_src_42_, lean_object* v_p_43_, lean_object* v_lo_44_, lean_object* v_hi_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg(v_src_42_, v_p_43_, v_lo_44_, v_hi_45_);
lean_dec(v_p_43_);
lean_dec_ref(v_src_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go(lean_object* v_s_47_, lean_object* v_src_48_, lean_object* v_p_49_, lean_object* v_lo_50_, lean_object* v_hi_51_, lean_object* v_h_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg(v_src_48_, v_p_49_, v_lo_50_, v_hi_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___boxed(lean_object* v_s_54_, lean_object* v_src_55_, lean_object* v_p_56_, lean_object* v_lo_57_, lean_object* v_hi_58_, lean_object* v_h_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go(v_s_54_, v_src_55_, v_p_56_, v_lo_57_, v_hi_58_, v_h_59_);
lean_dec(v_p_56_);
lean_dec_ref(v_src_55_);
lean_dec_ref(v_s_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___redArg(lean_object* v_src_61_, lean_object* v_p_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_array_get_size(v_src_61_);
v___x_65_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_lineIndex_go___redArg(v_src_61_, v_p_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___redArg___boxed(lean_object* v_src_66_, lean_object* v_p_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Markdown_InlineSource_lineIndex___redArg(v_src_66_, v_p_67_);
lean_dec(v_p_67_);
lean_dec_ref(v_src_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex(lean_object* v_s_69_, lean_object* v_src_70_, lean_object* v_p_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Markdown_InlineSource_lineIndex___redArg(v_src_70_, v_p_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_lineIndex___boxed(lean_object* v_s_73_, lean_object* v_src_74_, lean_object* v_p_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Markdown_InlineSource_lineIndex(v_s_73_, v_src_74_, v_p_75_);
lean_dec(v_p_75_);
lean_dec_ref(v_src_74_);
lean_dec_ref(v_s_73_);
return v_res_76_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
if (lean_obj_tag(v_x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
else
{
if (lean_obj_tag(v_x_78_) == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v_val_83_; uint32_t v___x_84_; uint32_t v___x_85_; uint8_t v___x_86_; 
v_val_82_ = lean_ctor_get(v_x_77_, 0);
v_val_83_ = lean_ctor_get(v_x_78_, 0);
v___x_84_ = lean_unbox_uint32(v_val_82_);
v___x_85_ = lean_unbox_uint32(v_val_83_);
v___x_86_ = lean_uint32_dec_eq(v___x_84_, v___x_85_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back(lean_object* v_s_91_, lean_object* v_line_92_, lean_object* v_p_93_, uint32_t v_c_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_String_Slice_Pos_prev_x3f(v_s_91_, v_p_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_inc(v_p_93_);
return v_p_93_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_108_; 
v_val_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_108_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_val_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_startInclusive_100_; uint8_t v___x_101_; 
v_startInclusive_100_ = lean_ctor_get(v_line_92_, 0);
v___x_101_ = lean_nat_dec_le(v_startInclusive_100_, v_val_96_);
if (v___x_101_ == 0)
{
lean_del_object(v___x_98_);
lean_dec(v_val_96_);
lean_inc(v_p_93_);
return v_p_93_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_102_ = l_String_Slice_Pos_get_x3f(v_s_91_, v_val_96_);
v___x_103_ = lean_box_uint32(v_c_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_103_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_107_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
uint8_t v___x_106_; 
v___x_106_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back_spec__0(v___x_102_, v___x_105_);
lean_dec_ref(v___x_105_);
lean_dec(v___x_102_);
if (v___x_106_ == 0)
{
lean_dec(v_val_96_);
lean_inc(v_p_93_);
return v_p_93_;
}
else
{
return v_val_96_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back___boxed(lean_object* v_s_109_, lean_object* v_line_110_, lean_object* v_p_111_, lean_object* v_c_112_){
_start:
{
uint32_t v_c_boxed_113_; lean_object* v_res_114_; 
v_c_boxed_113_ = lean_unbox_uint32(v_c_112_);
lean_dec(v_c_112_);
v_res_114_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back(v_s_109_, v_line_110_, v_p_111_, v_c_boxed_113_);
lean_dec(v_p_111_);
lean_dec_ref(v_line_110_);
lean_dec_ref(v_s_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd(lean_object* v_s_115_, lean_object* v_line_116_){
_start:
{
lean_object* v_endExclusive_117_; uint32_t v___x_118_; lean_object* v___x_119_; uint32_t v___x_120_; lean_object* v___x_121_; 
v_endExclusive_117_ = lean_ctor_get(v_line_116_, 1);
v___x_118_ = 10;
v___x_119_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back(v_s_115_, v_line_116_, v_endExclusive_117_, v___x_118_);
v___x_120_ = 13;
v___x_121_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_back(v_s_115_, v_line_116_, v___x_119_, v___x_120_);
lean_dec(v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd___boxed(lean_object* v_s_122_, lean_object* v_line_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd(v_s_122_, v_line_123_);
lean_dec_ref(v_line_123_);
lean_dec_ref(v_s_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip(lean_object* v_s_125_, lean_object* v_p1_126_, lean_object* v_p2_127_, lean_object* v_line_128_){
_start:
{
lean_object* v___y_130_; lean_object* v_startInclusive_135_; uint8_t v___x_136_; 
v_startInclusive_135_ = lean_ctor_get(v_line_128_, 0);
v___x_136_ = lean_nat_dec_le(v_startInclusive_135_, v_p1_126_);
if (v___x_136_ == 0)
{
lean_dec(v_p1_126_);
lean_inc(v_startInclusive_135_);
v___y_130_ = v_startInclusive_135_;
goto v___jp_129_;
}
else
{
v___y_130_ = v_p1_126_;
goto v___jp_129_;
}
v___jp_129_:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_textEnd(v_s_125_, v_line_128_);
lean_dec_ref(v_line_128_);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_p2_127_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_130_, v_p2_127_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; 
lean_dec(v_p2_127_);
v___x_134_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_130_, v___x_131_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip___boxed(lean_object* v_s_137_, lean_object* v_p1_138_, lean_object* v_p2_139_, lean_object* v_line_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip(v_s_137_, v_p1_138_, v_p2_139_, v_line_140_);
lean_dec_ref(v_s_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg(lean_object* v_upperBound_142_, lean_object* v___x_143_, lean_object* v_p2_144_, lean_object* v_s_145_, lean_object* v_p1_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_lt(v_a_147_, v_upperBound_142_);
if (v___x_149_ == 0)
{
lean_dec(v_a_147_);
lean_dec(v_p1_146_);
lean_dec(v_p2_144_);
return v_b_148_;
}
else
{
lean_object* v___x_150_; lean_object* v_startInclusive_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_150_ = lean_array_fget_borrowed(v___x_143_, v_a_147_);
v_startInclusive_151_ = lean_ctor_get(v___x_150_, 0);
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_add(v_p2_144_, v___x_152_);
v___x_154_ = lean_nat_dec_le(v___x_153_, v_startInclusive_151_);
lean_dec(v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc(v___x_150_);
lean_inc(v_p2_144_);
lean_inc(v_p1_146_);
v___x_155_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip(v_s_145_, v_p1_146_, v_p2_144_, v___x_150_);
v___x_156_ = lean_array_push(v_b_148_, v___x_155_);
v___x_157_ = lean_nat_add(v_a_147_, v___x_152_);
lean_dec(v_a_147_);
v_a_147_ = v___x_157_;
v_b_148_ = v___x_156_;
goto _start;
}
else
{
lean_dec(v_a_147_);
lean_dec(v_p1_146_);
lean_dec(v_p2_144_);
return v_b_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg___boxed(lean_object* v_upperBound_159_, lean_object* v___x_160_, lean_object* v_p2_161_, lean_object* v_s_162_, lean_object* v_p1_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg(v_upperBound_159_, v___x_160_, v_p2_161_, v_s_162_, v_p1_163_, v_a_164_, v_b_165_);
lean_dec_ref(v_s_162_);
lean_dec_ref(v___x_160_);
lean_dec(v_upperBound_159_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_linesBetween(lean_object* v_s_167_, lean_object* v_src_168_, lean_object* v_p1_169_, lean_object* v_p2_170_){
_start:
{
lean_object* v_i0_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_i0_171_ = l_Lean_Markdown_InlineSource_lineIndex___redArg(v_src_168_, v_p1_169_);
v___x_172_ = lean_array_get_size(v_src_168_);
v___x_173_ = lean_nat_dec_lt(v_i0_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_i0_171_);
v___x_174_ = l_Lean_Markdown_subsliceClamped___redArg(v_p1_169_, v_p2_170_);
v___x_175_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_out_180_; lean_object* v___x_181_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_add(v_i0_171_, v___x_176_);
v___x_178_ = lean_array_fget_borrowed(v_src_168_, v_i0_171_);
lean_dec(v_i0_171_);
lean_inc(v___x_178_);
lean_inc(v_p2_170_);
lean_inc(v_p1_169_);
v___x_179_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_linesBetween_clip(v_s_167_, v_p1_169_, v_p2_170_, v___x_178_);
v_out_180_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_179_);
v___x_181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg(v___x_172_, v_src_168_, v_p2_170_, v_s_167_, v_p1_169_, v___x_177_, v_out_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_linesBetween___boxed(lean_object* v_s_182_, lean_object* v_src_183_, lean_object* v_p1_184_, lean_object* v_p2_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Markdown_InlineSource_linesBetween(v_s_182_, v_src_183_, v_p1_184_, v_p2_185_);
lean_dec_ref(v_src_183_);
lean_dec_ref(v_s_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0(lean_object* v_upperBound_187_, lean_object* v___x_188_, lean_object* v_p2_189_, lean_object* v_s_190_, lean_object* v_p1_191_, lean_object* v_inst_192_, lean_object* v_R_193_, lean_object* v_a_194_, lean_object* v_b_195_, lean_object* v_c_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___redArg(v_upperBound_187_, v___x_188_, v_p2_189_, v_s_190_, v_p1_191_, v_a_194_, v_b_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0___boxed(lean_object* v_upperBound_198_, lean_object* v___x_199_, lean_object* v_p2_200_, lean_object* v_s_201_, lean_object* v_p1_202_, lean_object* v_inst_203_, lean_object* v_R_204_, lean_object* v_a_205_, lean_object* v_b_206_, lean_object* v_c_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_InlineSource_linesBetween_spec__0(v_upperBound_198_, v___x_199_, v_p2_200_, v_s_201_, v_p1_202_, v_inst_203_, v_R_204_, v_a_205_, v_b_206_, v_c_207_);
lean_dec_ref(v_s_201_);
lean_dec_ref(v___x_199_);
lean_dec(v_upperBound_198_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(lean_object* v_s_209_, lean_object* v_input_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_endExclusive_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_endExclusive_212_ = lean_ctor_get(v_input_210_, 1);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_a_211_, v___x_213_);
v___x_215_ = lean_nat_dec_le(v___x_214_, v_endExclusive_212_);
lean_dec(v___x_214_);
if (v___x_215_ == 0)
{
return v_a_211_;
}
else
{
lean_object* v_str_216_; lean_object* v_startInclusive_217_; lean_object* v___x_223_; uint32_t v___x_224_; uint32_t v___x_225_; uint8_t v___x_226_; 
v_str_216_ = lean_ctor_get(v_s_209_, 0);
v_startInclusive_217_ = lean_ctor_get(v_s_209_, 1);
v___x_223_ = lean_nat_add(v_startInclusive_217_, v_a_211_);
v___x_224_ = lean_string_utf8_get_fast(v_str_216_, v___x_223_);
lean_dec(v___x_223_);
v___x_225_ = 32;
v___x_226_ = lean_uint32_dec_eq(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 9;
v___x_228_ = lean_uint32_dec_eq(v___x_224_, v___x_227_);
if (v___x_228_ == 0)
{
return v_a_211_;
}
else
{
goto v___jp_218_;
}
}
else
{
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_nat_add(v_startInclusive_217_, v_a_211_);
lean_dec(v_a_211_);
v___x_220_ = lean_string_utf8_next_fast(v_str_216_, v___x_219_);
lean_dec(v___x_219_);
v___x_221_ = lean_nat_sub(v___x_220_, v_startInclusive_217_);
v_a_211_ = v___x_221_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg___boxed(lean_object* v_s_229_, lean_object* v_input_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(v_s_229_, v_input_230_, v_a_231_);
lean_dec_ref(v_input_230_);
lean_dec_ref(v_s_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces(lean_object* v_s_233_, lean_object* v_input_234_, lean_object* v_p_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(v_s_233_, v_input_234_, v_p_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces___boxed(lean_object* v_s_237_, lean_object* v_input_238_, lean_object* v_p_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces(v_s_237_, v_input_238_, v_p_239_);
lean_dec_ref(v_input_238_);
lean_dec_ref(v_s_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0(lean_object* v_s_241_, lean_object* v_input_242_, lean_object* v_inst_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(v_s_241_, v_input_242_, v_a_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___boxed(lean_object* v_s_246_, lean_object* v_input_247_, lean_object* v_inst_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0(v_s_246_, v_input_247_, v_inst_248_, v_a_249_);
lean_dec_ref(v_input_247_);
lean_dec_ref(v_s_246_);
return v_res_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineSource_ofLines___lam__0(uint32_t v___y_251_){
_start:
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 32;
v___x_253_ = lean_uint32_dec_eq(v___y_251_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 9;
v___x_255_ = lean_uint32_dec_eq(v___y_251_, v___x_254_);
if (v___x_255_ == 0)
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 13;
v___x_257_ = lean_uint32_dec_eq(v___y_251_, v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 10;
v___x_259_ = lean_uint32_dec_eq(v___y_251_, v___x_258_);
return v___x_259_;
}
else
{
return v___x_257_;
}
}
else
{
return v___x_255_;
}
}
else
{
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines___lam__0___boxed(lean_object* v___y_260_){
_start:
{
uint32_t v___y_365__boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v___y_365__boxed_261_ = lean_unbox_uint32(v___y_260_);
lean_dec(v___y_260_);
v_res_262_ = l_Lean_Markdown_InlineSource_ofLines___lam__0(v___y_365__boxed_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg(lean_object* v_s_264_, lean_object* v_count_265_, size_t v_sz_266_, size_t v_i_267_, lean_object* v_bs_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_269_ == 0)
{
return v_bs_268_;
}
else
{
lean_object* v_v_270_; lean_object* v_startInclusive_271_; lean_object* v_endExclusive_272_; lean_object* v___x_273_; lean_object* v_bs_x27_274_; lean_object* v___y_276_; lean_object* v___x_281_; lean_object* v_start_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_300_; 
v_v_270_ = lean_array_uget(v_bs_268_, v_i_267_);
v_startInclusive_271_ = lean_ctor_get(v_v_270_, 0);
v_endExclusive_272_ = lean_ctor_get(v_v_270_, 1);
lean_inc(v_endExclusive_272_);
v___x_273_ = lean_unsigned_to_nat(0u);
v_bs_x27_274_ = lean_array_uset(v_bs_268_, v_i_267_, v___x_273_);
v___x_281_ = lean_usize_to_nat(v_i_267_);
lean_inc(v_startInclusive_271_);
v_start_282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_InlineSource_0__Lean_Markdown_InlineSource_skipSpaces_spec__0___redArg(v_s_264_, v_v_270_, v_startInclusive_271_);
v_isSharedCheck_300_ = !lean_is_exclusive(v_v_270_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; 
v_unused_301_ = lean_ctor_get(v_v_270_, 1);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_v_270_, 0);
lean_dec(v_unused_302_);
v___x_284_ = v_v_270_;
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_v_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
v___jp_275_:
{
size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_267_, v___x_277_);
v___x_279_ = lean_array_uset(v_bs_x27_274_, v_i_267_, v___y_276_);
v_i_267_ = v___x_278_;
v_bs_268_ = v___x_279_;
goto _start;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v___x_281_, v___x_286_);
lean_dec(v___x_281_);
v___x_288_ = lean_nat_dec_lt(v___x_287_, v_count_265_);
lean_dec(v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_del_object(v___x_284_);
v___x_289_ = l_Lean_Markdown_subsliceClamped___redArg(v_start_282_, v_endExclusive_272_);
v___y_276_ = v___x_289_;
goto v___jp_275_;
}
else
{
lean_object* v_startInclusive_290_; lean_object* v_endExclusive_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v_startInclusive_290_ = lean_ctor_get(v_s_264_, 1);
v_endExclusive_291_ = lean_ctor_get(v_s_264_, 2);
v___x_292_ = lean_nat_sub(v_endExclusive_291_, v_startInclusive_290_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_292_);
lean_ctor_set(v___x_284_, 0, v___x_273_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_299_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Markdown_parseLineEnding_x3f(v_s_264_, v___x_294_, v_endExclusive_272_);
lean_dec_ref(v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Markdown_subsliceClamped___redArg(v_start_282_, v_endExclusive_272_);
v___y_276_ = v___x_296_;
goto v___jp_275_;
}
else
{
lean_object* v_val_297_; lean_object* v___x_298_; 
lean_dec(v_endExclusive_272_);
v_val_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_295_, 1);
v___x_298_ = l_Lean_Markdown_subsliceClamped___redArg(v_start_282_, v_val_297_);
v___y_276_ = v___x_298_;
goto v___jp_275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg___boxed(lean_object* v_s_303_, lean_object* v_count_304_, lean_object* v_sz_305_, lean_object* v_i_306_, lean_object* v_bs_307_){
_start:
{
size_t v_sz_boxed_308_; size_t v_i_boxed_309_; lean_object* v_res_310_; 
v_sz_boxed_308_ = lean_unbox_usize(v_sz_305_);
lean_dec(v_sz_305_);
v_i_boxed_309_ = lean_unbox_usize(v_i_306_);
lean_dec(v_i_306_);
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg(v_s_303_, v_count_304_, v_sz_boxed_308_, v_i_boxed_309_, v_bs_307_);
lean_dec(v_count_304_);
lean_dec_ref(v_s_303_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object* v_s_312_, lean_object* v_lines_313_){
_start:
{
lean_object* v___f_314_; lean_object* v_count_315_; size_t v_sz_316_; size_t v___x_317_; lean_object* v_out_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_lastIdx_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___f_314_ = ((lean_object*)(l_Lean_Markdown_InlineSource_ofLines___closed__0));
v_count_315_ = lean_array_get_size(v_lines_313_);
v_sz_316_ = lean_array_size(v_lines_313_);
v___x_317_ = ((size_t)0ULL);
v_out_318_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg(v_s_312_, v_count_315_, v_sz_316_, v___x_317_, v_lines_313_);
v___x_319_ = lean_array_get_size(v_out_318_);
v___x_320_ = lean_unsigned_to_nat(1u);
v_lastIdx_321_ = lean_nat_sub(v___x_319_, v___x_320_);
v___x_322_ = lean_array_fget_borrowed(v_out_318_, v_lastIdx_321_);
lean_inc(v___x_322_);
v___x_323_ = l_Lean_Markdown_trimTrailing(v_s_312_, v___x_322_, v___f_314_);
v___x_324_ = lean_array_fset(v_out_318_, v_lastIdx_321_, v___x_323_);
lean_dec(v_lastIdx_321_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_ofLines___boxed(lean_object* v_s_325_, lean_object* v_lines_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Markdown_InlineSource_ofLines(v_s_325_, v_lines_326_);
lean_dec_ref(v_s_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0(lean_object* v_s_328_, lean_object* v_count_329_, lean_object* v_as_330_, size_t v_sz_331_, size_t v_i_332_, lean_object* v_bs_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___redArg(v_s_328_, v_count_329_, v_sz_331_, v_i_332_, v_bs_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0___boxed(lean_object* v_s_335_, lean_object* v_count_336_, lean_object* v_as_337_, lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_bs_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Markdown_InlineSource_ofLines_spec__0(v_s_335_, v_count_336_, v_as_337_, v_sz_boxed_341_, v_i_boxed_342_, v_bs_340_);
lean_dec_ref(v_as_337_);
lean_dec(v_count_336_);
lean_dec_ref(v_s_335_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_instInhabited(lean_object* v_s_344_){
_start:
{
lean_object* v_startInclusive_345_; lean_object* v_endExclusive_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_startInclusive_345_ = lean_ctor_get(v_s_344_, 1);
v_endExclusive_346_ = lean_ctor_get(v_s_344_, 2);
v___x_347_ = lean_nat_sub(v_endExclusive_346_, v_startInclusive_345_);
lean_inc(v___x_347_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_348_);
v___x_350_ = l_Lean_Markdown_InlineSource_ofLines(v_s_344_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_instInhabited___boxed(lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Markdown_InlineSource_instInhabited(v_s_351_);
lean_dec_ref(v_s_351_);
return v_res_352_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Lines(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Lines(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_InlineSource(builtin);
}
#ifdef __cplusplus
}
#endif
