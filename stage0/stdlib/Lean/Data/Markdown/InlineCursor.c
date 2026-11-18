// Lean compiler output
// Module: Lean.Data.Markdown.InlineCursor
// Imports: public import Init.Data.Array.Basic public import Init.While import Init.Omega import Init.Data.String.OrderInstances public import Lean.Data.Markdown.Inline public import Lean.Data.Markdown.InlineSource
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_lineIndex___redArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineCursor_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineCursor_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Markdown_InlineCursor_front(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_charSubslice_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_charSubslice_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_drop1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_drop1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseChar_x3f(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseChar_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_takeSequence(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_takeSequence___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor_default(lean_object* v_s_1_){
_start:
{
lean_object* v_startInclusive_2_; lean_object* v_endExclusive_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_startInclusive_2_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_3_ = lean_ctor_get(v_s_1_, 2);
v___x_4_ = lean_nat_sub(v_endExclusive_3_, v_startInclusive_2_);
lean_inc(v___x_4_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
v___x_6_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_5_);
v___x_7_ = l_Lean_Markdown_InlineSource_ofLines(v_s_1_, v___x_6_);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_7_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor_default___boxed(lean_object* v_s_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Markdown_instInhabitedInlineCursor_default(v_s_10_);
lean_dec_ref(v_s_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor(lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Markdown_instInhabitedInlineCursor_default(v_a_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCursor___boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Markdown_instInhabitedInlineCursor(v_a_14_);
lean_dec_ref(v_a_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor___redArg(lean_object* v_src_16_, lean_object* v_startPos_17_, lean_object* v_stopPos_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = l_Lean_Markdown_InlineSource_lineIndex___redArg(v_src_16_, v_startPos_17_);
v___x_20_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_20_, 0, v_src_16_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
lean_ctor_set(v___x_20_, 2, v_startPos_17_);
lean_ctor_set(v___x_20_, 3, v_stopPos_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor(lean_object* v_s_21_, lean_object* v_src_22_, lean_object* v_startPos_23_, lean_object* v_stopPos_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Markdown_InlineSource_cursor___redArg(v_src_22_, v_startPos_23_, v_stopPos_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineSource_cursor___boxed(lean_object* v_s_26_, lean_object* v_src_27_, lean_object* v_startPos_28_, lean_object* v_stopPos_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Markdown_InlineSource_cursor(v_s_26_, v_src_27_, v_startPos_28_, v_stopPos_29_);
lean_dec_ref(v_s_26_);
return v_res_30_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineCursor_isEmpty___redArg(lean_object* v_cur_31_){
_start:
{
lean_object* v_startPos_32_; lean_object* v_stopPos_33_; uint8_t v___x_34_; 
v_startPos_32_ = lean_ctor_get(v_cur_31_, 2);
v_stopPos_33_ = lean_ctor_get(v_cur_31_, 3);
v___x_34_ = lean_nat_dec_le(v_stopPos_33_, v_startPos_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_isEmpty___redArg___boxed(lean_object* v_cur_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_cur_35_);
lean_dec_ref(v_cur_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_InlineCursor_isEmpty(lean_object* v_s_38_, lean_object* v_cur_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_cur_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_isEmpty___boxed(lean_object* v_s_41_, lean_object* v_cur_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Lean_Markdown_InlineCursor_isEmpty(v_s_41_, v_cur_42_);
lean_dec_ref(v_cur_42_);
lean_dec_ref(v_s_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front_x3f(lean_object* v_s_45_, lean_object* v_cur_46_){
_start:
{
lean_object* v_startPos_47_; lean_object* v_stopPos_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_startPos_47_ = lean_ctor_get(v_cur_46_, 2);
v_stopPos_48_ = lean_ctor_get(v_cur_46_, 3);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_startPos_47_, v___x_49_);
v___x_51_ = lean_nat_dec_le(v___x_50_, v_stopPos_48_);
lean_dec(v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = l_String_Slice_Pos_get_x3f(v_s_45_, v_startPos_47_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front_x3f___boxed(lean_object* v_s_54_, lean_object* v_cur_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_54_, v_cur_55_);
lean_dec_ref(v_cur_55_);
lean_dec_ref(v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT uint32_t l_Lean_Markdown_InlineCursor_front(lean_object* v_s_57_, lean_object* v_cur_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_57_, v_cur_58_);
if (lean_obj_tag(v___x_59_) == 0)
{
uint32_t v___x_60_; 
v___x_60_ = 65;
return v___x_60_;
}
else
{
lean_object* v_val_61_; uint32_t v___x_62_; 
v_val_61_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v___x_59_, 1);
v___x_62_ = lean_unbox_uint32(v_val_61_);
lean_dec(v_val_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_front___boxed(lean_object* v_s_63_, lean_object* v_cur_64_){
_start:
{
uint32_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_Markdown_InlineCursor_front(v_s_63_, v_cur_64_);
lean_dec_ref(v_cur_64_);
lean_dec_ref(v_s_63_);
v_r_66_ = lean_box_uint32(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice___redArg(lean_object* v_cur_67_){
_start:
{
lean_object* v_startPos_68_; lean_object* v_stopPos_69_; lean_object* v___x_70_; 
v_startPos_68_ = lean_ctor_get(v_cur_67_, 2);
lean_inc(v_startPos_68_);
v_stopPos_69_ = lean_ctor_get(v_cur_67_, 3);
lean_inc(v_stopPos_69_);
lean_dec_ref(v_cur_67_);
v___x_70_ = l_Lean_Markdown_subsliceClamped___redArg(v_startPos_68_, v_stopPos_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice(lean_object* v_s_71_, lean_object* v_cur_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Markdown_InlineCursor_toSubslice___redArg(v_cur_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_toSubslice___boxed(lean_object* v_s_74_, lean_object* v_cur_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Markdown_InlineCursor_toSubslice(v_s_74_, v_cur_75_);
lean_dec_ref(v_s_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_charSubslice_x3f(lean_object* v_s_77_, lean_object* v_cur_78_){
_start:
{
lean_object* v_startPos_79_; lean_object* v_stopPos_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_startPos_79_ = lean_ctor_get(v_cur_78_, 2);
v_stopPos_80_ = lean_ctor_get(v_cur_78_, 3);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_startPos_79_, v___x_81_);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_stopPos_80_);
lean_dec(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v_str_85_; lean_object* v_startInclusive_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_str_85_ = lean_ctor_get(v_s_77_, 0);
v_startInclusive_86_ = lean_ctor_get(v_s_77_, 1);
v___x_87_ = lean_nat_add(v_startInclusive_86_, v_startPos_79_);
v___x_88_ = lean_string_utf8_next_fast(v_str_85_, v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_nat_sub(v___x_88_, v_startInclusive_86_);
lean_inc(v_startPos_79_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_startPos_79_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_charSubslice_x3f___boxed(lean_object* v_s_92_, lean_object* v_cur_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_92_, v_cur_93_);
lean_dec_ref(v_cur_93_);
lean_dec_ref(v_s_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_drop1(lean_object* v_s_95_, lean_object* v_cur_96_){
_start:
{
lean_object* v_source_97_; lean_object* v_line_98_; lean_object* v_startPos_99_; lean_object* v_stopPos_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_source_97_ = lean_ctor_get(v_cur_96_, 0);
v_line_98_ = lean_ctor_get(v_cur_96_, 1);
v_startPos_99_ = lean_ctor_get(v_cur_96_, 2);
v_stopPos_100_ = lean_ctor_get(v_cur_96_, 3);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_startPos_99_, v___x_101_);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_stopPos_100_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
return v_cur_96_;
}
else
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_134_; 
lean_inc(v_stopPos_100_);
lean_inc(v_startPos_99_);
lean_inc(v_line_98_);
lean_inc_ref(v_source_97_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_cur_96_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; lean_object* v_unused_138_; 
v_unused_135_ = lean_ctor_get(v_cur_96_, 3);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_cur_96_, 2);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_cur_96_, 1);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_cur_96_, 0);
lean_dec(v_unused_138_);
v___x_105_ = v_cur_96_;
v_isShared_106_ = v_isSharedCheck_134_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_cur_96_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_134_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_str_107_; lean_object* v_startInclusive_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_q_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_str_107_ = lean_ctor_get(v_s_95_, 0);
v_startInclusive_108_ = lean_ctor_get(v_s_95_, 1);
v___x_109_ = lean_nat_add(v_startInclusive_108_, v_startPos_99_);
lean_dec(v_startPos_99_);
v___x_110_ = lean_string_utf8_next_fast(v_str_107_, v___x_109_);
lean_dec(v___x_109_);
v_q_111_ = lean_nat_sub(v___x_110_, v_startInclusive_108_);
v___x_112_ = lean_array_get_size(v_source_97_);
v___x_113_ = lean_nat_dec_lt(v_line_98_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v_q_111_);
v___x_115_ = v___x_105_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_source_97_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_line_98_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_q_111_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_stopPos_100_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_117_; lean_object* v_endExclusive_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_117_ = lean_array_fget_borrowed(v_source_97_, v_line_98_);
v_endExclusive_118_ = lean_ctor_get(v___x_117_, 1);
v___x_119_ = lean_nat_add(v_q_111_, v___x_101_);
v___x_120_ = lean_nat_dec_le(v___x_119_, v_endExclusive_118_);
lean_dec(v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_nat_add(v_line_98_, v___x_101_);
lean_dec(v_line_98_);
v___x_122_ = lean_nat_dec_lt(v___x_121_, v___x_112_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v_q_111_);
lean_ctor_set(v___x_105_, 1, v___x_121_);
v___x_124_ = v___x_105_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_source_97_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_q_111_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_stopPos_100_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v_startInclusive_127_; lean_object* v___x_129_; 
lean_dec(v_q_111_);
v___x_126_ = lean_array_fget_borrowed(v_source_97_, v___x_121_);
v_startInclusive_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_startInclusive_127_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v_startInclusive_127_);
lean_ctor_set(v___x_105_, 1, v___x_121_);
v___x_129_ = v___x_105_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_source_97_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_startInclusive_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_stopPos_100_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v___x_132_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v_q_111_);
v___x_132_ = v___x_105_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_source_97_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_line_98_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_q_111_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_stopPos_100_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_drop1___boxed(lean_object* v_s_139_, lean_object* v_cur_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Markdown_InlineCursor_drop1(v_s_139_, v_cur_140_);
lean_dec_ref(v_s_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(lean_object* v_s_142_, lean_object* v_cur_143_){
_start:
{
lean_object* v_startPos_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_startPos_144_ = lean_ctor_get(v_cur_143_, 2);
lean_inc(v_startPos_144_);
lean_inc_ref(v_cur_143_);
v___x_145_ = l_Lean_Markdown_InlineCursor_toSubslice___redArg(v_cur_143_);
v___x_146_ = l_Lean_Markdown_parseLineEnding_x3f(v_s_142_, v___x_145_, v_startPos_144_);
lean_dec_ref(v___x_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v___x_147_; 
lean_dec(v_startPos_144_);
lean_dec_ref(v_cur_143_);
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_val_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_165_; 
v_val_148_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_165_ == 0)
{
v___x_150_ = v___x_146_;
v_isShared_151_ = v_isSharedCheck_165_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_val_148_);
lean_dec(v___x_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_165_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_after_153_; lean_object* v___x_159_; lean_object* v_startPos_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_159_ = l_Lean_Markdown_InlineCursor_drop1(v_s_142_, v_cur_143_);
v_startPos_160_ = lean_ctor_get(v___x_159_, 2);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_startPos_160_, v___x_161_);
v___x_163_ = lean_nat_dec_le(v___x_162_, v_val_148_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
v_after_153_ = v___x_159_;
goto v___jp_152_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Markdown_InlineCursor_drop1(v_s_142_, v___x_159_);
v_after_153_ = v___x_164_;
goto v___jp_152_;
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_Markdown_subsliceClamped___redArg(v_startPos_144_, v_val_148_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_after_153_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_155_);
v___x_157_ = v___x_150_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f___boxed(lean_object* v_s_166_, lean_object* v_cur_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_166_, v_cur_167_);
lean_dec_ref(v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go(lean_object* v_s_169_, lean_object* v_p_170_, lean_object* v_q_171_, lean_object* v_lineEnd_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_q_171_, v___x_173_);
v___x_175_ = lean_nat_dec_le(v___x_174_, v_lineEnd_172_);
lean_dec(v___x_174_);
if (v___x_175_ == 0)
{
lean_dec_ref(v_p_170_);
return v_q_171_;
}
else
{
lean_object* v_str_176_; lean_object* v_startInclusive_177_; lean_object* v___x_178_; uint32_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_str_176_ = lean_ctor_get(v_s_169_, 0);
v_startInclusive_177_ = lean_ctor_get(v_s_169_, 1);
v___x_178_ = lean_nat_add(v_startInclusive_177_, v_q_171_);
v___x_179_ = lean_string_utf8_get_fast(v_str_176_, v___x_178_);
v___x_180_ = lean_box_uint32(v___x_179_);
lean_inc_ref(v_p_170_);
v___x_181_ = lean_apply_1(v_p_170_, v___x_180_);
v___x_182_ = lean_unbox(v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v___x_178_);
lean_dec_ref(v_p_170_);
return v_q_171_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_q_171_);
v___x_183_ = lean_string_utf8_next_fast(v_str_176_, v___x_178_);
lean_dec(v___x_178_);
v___x_184_ = lean_nat_sub(v___x_183_, v_startInclusive_177_);
v_q_171_ = v___x_184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___boxed(lean_object* v_s_186_, lean_object* v_p_187_, lean_object* v_q_188_, lean_object* v_lineEnd_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go(v_s_186_, v_p_187_, v_q_188_, v_lineEnd_189_);
lean_dec(v_lineEnd_189_);
lean_dec_ref(v_s_186_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile(lean_object* v_s_191_, lean_object* v_cur_192_, lean_object* v_p_193_){
_start:
{
lean_object* v_source_194_; lean_object* v_line_195_; lean_object* v_startPos_196_; lean_object* v_stopPos_197_; lean_object* v___y_199_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_source_194_ = lean_ctor_get(v_cur_192_, 0);
v_line_195_ = lean_ctor_get(v_cur_192_, 1);
v_startPos_196_ = lean_ctor_get(v_cur_192_, 2);
v_stopPos_197_ = lean_ctor_get(v_cur_192_, 3);
v___x_242_ = lean_array_get_size(v_source_194_);
v___x_243_ = lean_nat_dec_lt(v_line_195_, v___x_242_);
if (v___x_243_ == 0)
{
lean_inc(v_stopPos_197_);
v___y_199_ = v_stopPos_197_;
goto v___jp_198_;
}
else
{
lean_object* v___x_244_; lean_object* v_endExclusive_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_244_ = lean_array_fget_borrowed(v_source_194_, v_line_195_);
v_endExclusive_245_ = lean_ctor_get(v___x_244_, 1);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_endExclusive_245_, v___x_246_);
v___x_248_ = lean_nat_dec_le(v___x_247_, v_stopPos_197_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
lean_inc(v_stopPos_197_);
v___y_199_ = v_stopPos_197_;
goto v___jp_198_;
}
else
{
lean_inc(v_endExclusive_245_);
v___y_199_ = v_endExclusive_245_;
goto v___jp_198_;
}
}
v___jp_198_:
{
lean_object* v_pos_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
lean_inc(v_startPos_196_);
lean_inc_ref(v_p_193_);
v_pos_200_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go(v_s_191_, v_p_193_, v_startPos_196_, v___y_199_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_pos_200_, v___x_201_);
v___x_203_ = lean_nat_dec_le(v___x_202_, v___y_199_);
lean_dec(v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v_decide_204_; 
v_decide_204_ = lean_nat_dec_eq(v___y_199_, v_stopPos_197_);
if (v_decide_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_pos_200_);
v___x_205_ = l_String_Slice_Pos_prev_x3f(v_s_191_, v___y_199_);
lean_dec(v___y_199_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_dec_ref(v_p_193_);
return v_cur_192_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_215_; 
lean_inc(v_stopPos_197_);
lean_inc(v_line_195_);
lean_inc_ref(v_source_194_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_cur_192_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; 
v_unused_216_ = lean_ctor_get(v_cur_192_, 3);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_cur_192_, 2);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_cur_192_, 1);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_cur_192_, 0);
lean_dec(v_unused_219_);
v___x_207_ = v_cur_192_;
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_cur_192_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_val_209_; lean_object* v___x_211_; 
v_val_209_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_205_, 1);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v_val_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_source_194_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_line_195_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_val_209_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_stopPos_197_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Markdown_InlineCursor_drop1(v_s_191_, v___x_211_);
v_cur_192_ = v___x_212_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_inc(v_stopPos_197_);
lean_inc(v_line_195_);
lean_inc_ref(v_source_194_);
lean_dec(v___y_199_);
lean_dec_ref(v_p_193_);
v_isSharedCheck_226_ = !lean_is_exclusive(v_cur_192_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; 
v_unused_227_ = lean_ctor_get(v_cur_192_, 3);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_cur_192_, 2);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_cur_192_, 1);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_cur_192_, 0);
lean_dec(v_unused_230_);
v___x_221_ = v_cur_192_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_dec(v_cur_192_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 2, v_pos_200_);
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_source_194_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_line_195_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_pos_200_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_stopPos_197_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_inc(v_stopPos_197_);
lean_inc(v_line_195_);
lean_inc_ref(v_source_194_);
lean_dec(v___y_199_);
lean_dec_ref(v_p_193_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_cur_192_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_238_ = lean_ctor_get(v_cur_192_, 3);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_cur_192_, 2);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_cur_192_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_cur_192_, 0);
lean_dec(v_unused_241_);
v___x_232_ = v_cur_192_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_dec(v_cur_192_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 2, v_pos_200_);
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_source_194_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_line_195_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_pos_200_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_stopPos_197_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___boxed(lean_object* v_s_249_, lean_object* v_cur_250_, lean_object* v_p_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Markdown_InlineCursor_skipWhile(v_s_249_, v_cur_250_, v_p_251_);
lean_dec_ref(v_s_249_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
if (lean_obj_tag(v_x_254_) == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
else
{
if (lean_obj_tag(v_x_254_) == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
else
{
lean_object* v_val_258_; lean_object* v_val_259_; uint32_t v___x_260_; uint32_t v___x_261_; uint8_t v___x_262_; 
v_val_258_ = lean_ctor_get(v_x_253_, 0);
v_val_259_ = lean_ctor_get(v_x_254_, 0);
v___x_260_ = lean_unbox_uint32(v_val_258_);
v___x_261_ = lean_unbox_uint32(v_val_259_);
v___x_262_ = lean_uint32_dec_eq(v___x_260_, v___x_261_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0___boxed(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0(v_x_263_, v_x_264_);
lean_dec(v_x_264_);
lean_dec(v_x_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseChar_x3f(lean_object* v_s_267_, uint32_t v_c_268_, lean_object* v_cur_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_270_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_267_, v_cur_269_);
v___x_271_ = lean_box_uint32(v_c_268_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0(v___x_270_, v___x_272_);
lean_dec_ref_known(v___x_272_, 1);
lean_dec(v___x_270_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_cur_269_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Markdown_InlineCursor_charSubslice_x3f(v_s_267_, v_cur_269_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_cur_269_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
v_val_277_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_279_ = v___x_275_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_val_277_);
lean_dec(v___x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = l_Lean_Markdown_InlineCursor_drop1(v_s_267_, v_cur_269_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_val_277_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_282_);
v___x_284_ = v___x_279_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_parseChar_x3f___boxed(lean_object* v_s_287_, lean_object* v_c_288_, lean_object* v_cur_289_){
_start:
{
uint32_t v_c_boxed_290_; lean_object* v_res_291_; 
v_c_boxed_290_ = lean_unbox_uint32(v_c_288_);
lean_dec(v_c_288_);
v_res_291_ = l_Lean_Markdown_InlineCursor_parseChar_x3f(v_s_287_, v_c_boxed_290_, v_cur_289_);
lean_dec_ref(v_s_287_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go(lean_object* v_s_292_, uint32_t v_c_293_, lean_object* v_cur_294_, lean_object* v_n_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_292_, v_cur_294_);
v___x_297_ = lean_box_uint32(v_c_293_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = l_instBEqOption_beq___at___00Lean_Markdown_InlineCursor_parseChar_x3f_spec__0(v___x_296_, v___x_298_);
lean_dec_ref_known(v___x_298_, 1);
lean_dec(v___x_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_cur_294_);
lean_ctor_set(v___x_300_, 1, v_n_295_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = l_Lean_Markdown_InlineCursor_drop1(v_s_292_, v_cur_294_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_n_295_, v___x_302_);
lean_dec(v_n_295_);
v_cur_294_ = v___x_301_;
v_n_295_ = v___x_303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go___boxed(lean_object* v_s_305_, lean_object* v_c_306_, lean_object* v_cur_307_, lean_object* v_n_308_){
_start:
{
uint32_t v_c_boxed_309_; lean_object* v_res_310_; 
v_c_boxed_309_ = lean_unbox_uint32(v_c_306_);
lean_dec(v_c_306_);
v_res_310_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go(v_s_305_, v_c_boxed_309_, v_cur_307_, v_n_308_);
lean_dec_ref(v_s_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_takeSequence(lean_object* v_s_311_, uint32_t v_c_312_, lean_object* v_cur_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_takeSequence_go(v_s_311_, v_c_312_, v_cur_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_takeSequence___boxed(lean_object* v_s_316_, lean_object* v_c_317_, lean_object* v_cur_318_){
_start:
{
uint32_t v_c_boxed_319_; lean_object* v_res_320_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_317_);
lean_dec(v_c_317_);
v_res_320_ = l_Lean_Markdown_InlineCursor_takeSequence(v_s_316_, v_c_boxed_319_, v_cur_318_);
lean_dec_ref(v_s_316_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg___lam__0(lean_object* v_toPure_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_refs_323_; lean_object* v___x_324_; 
v_refs_323_ = lean_ctor_get(v_a_322_, 0);
lean_inc_ref(v_refs_323_);
lean_dec_ref(v_a_322_);
v___x_324_ = lean_apply_2(v_toPure_321_, lean_box(0), v_refs_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg(lean_object* v_inst_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_toPure_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_325_, 0);
lean_inc_ref(v_toApplicative_327_);
v_toBind_328_ = lean_ctor_get(v_inst_325_, 1);
lean_inc(v_toBind_328_);
lean_dec_ref(v_inst_325_);
v_toPure_329_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc_n(v_toPure_329_, 2);
lean_dec_ref(v_toApplicative_327_);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_Markdown_refTable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_330_, 0, v_toPure_329_);
lean_inc_ref(v_a_326_);
v___x_331_ = lean_apply_2(v_toPure_329_, lean_box(0), v_a_326_);
v___x_332_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_331_, v___f_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___redArg___boxed(lean_object* v_inst_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Markdown_refTable___redArg(v_inst_333_, v_a_334_);
lean_dec_ref(v_a_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable(lean_object* v_s_336_, lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v_toPure_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_338_, 0);
lean_inc_ref(v_toApplicative_340_);
v_toBind_341_ = lean_ctor_get(v_inst_338_, 1);
lean_inc(v_toBind_341_);
lean_dec_ref(v_inst_338_);
v_toPure_342_ = lean_ctor_get(v_toApplicative_340_, 1);
lean_inc_n(v_toPure_342_, 2);
lean_dec_ref(v_toApplicative_340_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Markdown_refTable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_343_, 0, v_toPure_342_);
lean_inc_ref(v_a_339_);
v___x_344_ = lean_apply_2(v_toPure_342_, lean_box(0), v_a_339_);
v___x_345_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v___x_344_, v___f_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_refTable___boxed(lean_object* v_s_346_, lean_object* v_m_347_, lean_object* v_inst_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Markdown_refTable(v_s_346_, v_m_347_, v_inst_348_, v_a_349_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_s_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg___lam__0(lean_object* v_toPure_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_src_353_; lean_object* v___x_354_; 
v_src_353_ = lean_ctor_get(v_a_352_, 1);
lean_inc_ref(v_src_353_);
lean_dec_ref(v_a_352_);
v___x_354_ = lean_apply_2(v_toPure_351_, lean_box(0), v_src_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg(lean_object* v_inst_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_toApplicative_357_; lean_object* v_toBind_358_; lean_object* v_toPure_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_toApplicative_357_ = lean_ctor_get(v_inst_355_, 0);
lean_inc_ref(v_toApplicative_357_);
v_toBind_358_ = lean_ctor_get(v_inst_355_, 1);
lean_inc(v_toBind_358_);
lean_dec_ref(v_inst_355_);
v_toPure_359_ = lean_ctor_get(v_toApplicative_357_, 1);
lean_inc_n(v_toPure_359_, 2);
lean_dec_ref(v_toApplicative_357_);
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Markdown_inlineSource___redArg___lam__0), 2, 1);
lean_closure_set(v___f_360_, 0, v_toPure_359_);
lean_inc_ref(v_a_356_);
v___x_361_ = lean_apply_2(v_toPure_359_, lean_box(0), v_a_356_);
v___x_362_ = lean_apply_4(v_toBind_358_, lean_box(0), lean_box(0), v___x_361_, v___f_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___redArg___boxed(lean_object* v_inst_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Markdown_inlineSource___redArg(v_inst_363_, v_a_364_);
lean_dec_ref(v_a_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource(lean_object* v_s_366_, lean_object* v_m_367_, lean_object* v_inst_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_toApplicative_370_; lean_object* v_toBind_371_; lean_object* v_toPure_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_toApplicative_370_ = lean_ctor_get(v_inst_368_, 0);
lean_inc_ref(v_toApplicative_370_);
v_toBind_371_ = lean_ctor_get(v_inst_368_, 1);
lean_inc(v_toBind_371_);
lean_dec_ref(v_inst_368_);
v_toPure_372_ = lean_ctor_get(v_toApplicative_370_, 1);
lean_inc_n(v_toPure_372_, 2);
lean_dec_ref(v_toApplicative_370_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Markdown_inlineSource___redArg___lam__0), 2, 1);
lean_closure_set(v___f_373_, 0, v_toPure_372_);
lean_inc_ref(v_a_369_);
v___x_374_ = lean_apply_2(v_toPure_372_, lean_box(0), v_a_369_);
v___x_375_ = lean_apply_4(v_toBind_371_, lean_box(0), lean_box(0), v___x_374_, v___f_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_inlineSource___boxed(lean_object* v_s_376_, lean_object* v_m_377_, lean_object* v_inst_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Markdown_inlineSource(v_s_376_, v_m_377_, v_inst_378_, v_a_379_);
lean_dec_ref(v_a_379_);
lean_dec_ref(v_s_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___lam__0(lean_object* v_toPure_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_extensions_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_extensions_383_ = lean_ctor_get_uint8(v_a_382_, sizeof(void*)*2);
v___x_384_ = lean_box(v_extensions_383_);
v___x_385_ = lean_apply_2(v_toPure_381_, lean_box(0), v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___lam__0___boxed(lean_object* v_toPure_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Markdown_extensions___redArg___lam__0(v_toPure_386_, v_a_387_);
lean_dec_ref(v_a_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg(lean_object* v_inst_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_toApplicative_391_; lean_object* v_toBind_392_; lean_object* v_toPure_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_toApplicative_391_ = lean_ctor_get(v_inst_389_, 0);
lean_inc_ref(v_toApplicative_391_);
v_toBind_392_ = lean_ctor_get(v_inst_389_, 1);
lean_inc(v_toBind_392_);
lean_dec_ref(v_inst_389_);
v_toPure_393_ = lean_ctor_get(v_toApplicative_391_, 1);
lean_inc_n(v_toPure_393_, 2);
lean_dec_ref(v_toApplicative_391_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_Markdown_extensions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_394_, 0, v_toPure_393_);
lean_inc_ref(v_a_390_);
v___x_395_ = lean_apply_2(v_toPure_393_, lean_box(0), v_a_390_);
v___x_396_ = lean_apply_4(v_toBind_392_, lean_box(0), lean_box(0), v___x_395_, v___f_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___redArg___boxed(lean_object* v_inst_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Markdown_extensions___redArg(v_inst_397_, v_a_398_);
lean_dec_ref(v_a_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions(lean_object* v_s_400_, lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_toApplicative_404_; lean_object* v_toBind_405_; lean_object* v_toPure_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_toApplicative_404_ = lean_ctor_get(v_inst_402_, 0);
lean_inc_ref(v_toApplicative_404_);
v_toBind_405_ = lean_ctor_get(v_inst_402_, 1);
lean_inc(v_toBind_405_);
lean_dec_ref(v_inst_402_);
v_toPure_406_ = lean_ctor_get(v_toApplicative_404_, 1);
lean_inc_n(v_toPure_406_, 2);
lean_dec_ref(v_toApplicative_404_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Markdown_extensions___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_407_, 0, v_toPure_406_);
lean_inc_ref(v_a_403_);
v___x_408_ = lean_apply_2(v_toPure_406_, lean_box(0), v_a_403_);
v___x_409_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v___x_408_, v___f_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extensions___boxed(lean_object* v_s_410_, lean_object* v_m_411_, lean_object* v_inst_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Markdown_extensions(v_s_410_, v_m_411_, v_inst_412_, v_a_413_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_s_410_);
return v_res_414_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin) {
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
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_InlineCursor(builtin);
}
#ifdef __cplusplus
}
#endif
