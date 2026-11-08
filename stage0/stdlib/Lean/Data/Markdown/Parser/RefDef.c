// Lean compiler output
// Module: Lean.Data.Markdown.Parser.RefDef
// Imports: public import Init.While public import Lean.Data.Markdown.Block public import Lean.Data.Markdown.InlineCursor import Lean.Data.Markdown.Text import Lean.Data.Markdown.Parser.LinkSyntax
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
lean_object* l_Lean_Markdown_InlineCursor_front_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineCursor_drop1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_linesBetween(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Markdown_isAsciiPunctuation(uint32_t);
lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_cursor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineCursor_parseChar_x3f(lean_object*, uint32_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLinkDestination_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLinkTitle_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_InlineCursor_isEmpty___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_startPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Markdown_parseLinkLabel_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_parseLinkLabel_x3f___closed__0 = (const lean_object*)&l_Lean_Markdown_parseLinkLabel_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_parseLinkLabel_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Markdown_parseLinkLabel_x3f___closed__0_value)}};
static const lean_object* l_Lean_Markdown_parseLinkLabel_x3f___closed__1 = (const lean_object*)&l_Lean_Markdown_parseLinkLabel_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkLabel_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkLabel_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkRefDef_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkRefDef_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_extractRefDefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_extractRefDefs___closed__0 = (const lean_object*)&l_Lean_Markdown_extractRefDefs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_extractRefDefs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_extractRefDefs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0(lean_object* v_fst_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_____r_4_, uint8_t v_sawNonWs_5_, uint8_t v_sawNewline_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_fst_1_, v___x_7_);
v___x_9_ = lean_box(v_sawNonWs_5_);
v___x_10_ = lean_box(v_sawNewline_6_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_8_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_2_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_3_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_____r_20_, lean_object* v_sawNonWs_21_, lean_object* v_sawNewline_22_){
_start:
{
uint8_t v_sawNonWs_boxed_23_; uint8_t v_sawNewline_boxed_24_; lean_object* v_res_25_; 
v_sawNonWs_boxed_23_ = lean_unbox(v_sawNonWs_21_);
v_sawNewline_boxed_24_ = lean_unbox(v_sawNewline_22_);
v_res_25_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0(v_fst_17_, v___x_18_, v___x_19_, v_____r_20_, v_sawNonWs_boxed_23_, v_sawNewline_boxed_24_);
lean_dec(v_fst_17_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg(lean_object* v_s_26_, lean_object* v_labelStart_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___y_30_; lean_object* v_snd_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_187_; 
v_snd_43_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_a_28_, 0);
lean_dec(v_unused_188_);
v___x_45_ = v_a_28_;
v_isShared_46_ = v_isSharedCheck_187_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_snd_43_);
lean_dec(v_a_28_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_187_;
goto v_resetjp_44_;
}
v___jp_29_:
{
if (lean_obj_tag(v___y_30_) == 0)
{
lean_object* v___x_31_; 
lean_dec(v_labelStart_27_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
else
{
lean_object* v_val_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_42_; 
v_val_32_ = lean_ctor_get(v___y_30_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___y_30_);
if (v_isSharedCheck_42_ == 0)
{
v___x_34_ = v___y_30_;
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_val_32_);
lean_dec(v___y_30_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
if (lean_obj_tag(v_val_32_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_38_; 
lean_dec(v_labelStart_27_);
v_a_36_ = lean_ctor_get(v_val_32_, 0);
lean_inc(v_a_36_);
lean_dec_ref_known(v_val_32_, 1);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v_a_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
else
{
lean_object* v_a_40_; 
lean_del_object(v___x_34_);
v_a_40_ = lean_ctor_get(v_val_32_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v_val_32_, 1);
v_a_28_ = v_a_40_;
goto _start;
}
}
}
}
v_resetjp_44_:
{
lean_object* v_snd_47_; lean_object* v_snd_48_; lean_object* v_fst_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_185_; 
v_snd_47_ = lean_ctor_get(v_snd_43_, 1);
lean_inc(v_snd_47_);
v_snd_48_ = lean_ctor_get(v_snd_47_, 1);
lean_inc(v_snd_48_);
v_fst_49_ = lean_ctor_get(v_snd_43_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_snd_43_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_snd_43_, 1);
lean_dec(v_unused_186_);
v___x_51_ = v_snd_43_;
v_isShared_52_ = v_isSharedCheck_185_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_fst_49_);
lean_dec(v_snd_43_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_185_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_fst_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_183_; 
v_fst_53_ = lean_ctor_get(v_snd_47_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_snd_47_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_snd_47_, 1);
lean_dec(v_unused_184_);
v___x_55_ = v_snd_47_;
v_isShared_56_ = v_isSharedCheck_183_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_fst_53_);
lean_dec(v_snd_47_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_183_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_fst_57_; lean_object* v_snd_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_182_; 
v_fst_57_ = lean_ctor_get(v_snd_48_, 0);
v_snd_58_ = lean_ctor_get(v_snd_48_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_snd_48_);
if (v_isSharedCheck_182_ == 0)
{
v___x_60_ = v_snd_48_;
v_isShared_61_ = v_isSharedCheck_182_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_snd_58_);
lean_inc(v_fst_57_);
lean_dec(v_snd_48_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_182_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_unsigned_to_nat(1000u);
v___x_64_ = lean_nat_dec_lt(v_fst_53_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_66_; 
lean_dec(v_labelStart_27_);
if (v_isShared_61_ == 0)
{
v___x_66_ = v___x_60_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_fst_57_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_snd_58_);
v___x_66_ = v_reuseFailAlloc_77_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_66_);
v___x_68_ = v___x_55_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_fst_53_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_76_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_68_);
v___x_70_ = v___x_51_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_fst_49_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_75_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_70_);
lean_ctor_set(v___x_45_, 0, v___x_62_);
v___x_72_ = v___x_45_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_26_, v_fst_49_);
if (lean_obj_tag(v___x_78_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_168_; 
v_val_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_168_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_168_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_168_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint8_t v_sawNonWs_83_; lean_object* v___x_84_; uint32_t v___x_151_; uint32_t v___x_152_; uint8_t v___x_153_; 
v_sawNonWs_83_ = 0;
lean_inc(v_fst_49_);
v___x_84_ = l_Lean_Markdown_InlineCursor_drop1(v_s_26_, v_fst_49_);
v___x_151_ = 92;
v___x_152_ = lean_unbox_uint32(v_val_79_);
v___x_153_ = lean_uint32_dec_eq(v___x_152_, v___x_151_);
if (v___x_153_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_26_, v___x_84_);
if (lean_obj_tag(v___x_154_) == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v_val_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v_val_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = lean_unbox_uint32(v_val_155_);
lean_dec(v_val_155_);
v___x_157_ = l_Lean_Markdown_isAsciiPunctuation(v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_del_object(v___x_81_);
lean_dec(v_val_79_);
lean_del_object(v___x_60_);
lean_dec(v_snd_58_);
lean_dec(v_fst_57_);
lean_del_object(v___x_55_);
lean_del_object(v___x_51_);
lean_dec(v_fst_49_);
lean_del_object(v___x_45_);
v___x_158_ = l_Lean_Markdown_InlineCursor_drop1(v_s_26_, v___x_84_);
v___x_159_ = lean_unsigned_to_nat(2u);
v___x_160_ = lean_nat_add(v_fst_53_, v___x_159_);
lean_dec(v_fst_53_);
v___x_161_ = lean_box(v___x_64_);
v___x_162_ = lean_box(v_sawNonWs_83_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_160_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_158_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_62_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v_a_28_ = v___x_166_;
goto _start;
}
}
}
v___jp_85_:
{
lean_object* v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_box(0);
v___x_87_ = lean_unbox(v_fst_57_);
lean_dec(v_fst_57_);
v___x_88_ = lean_unbox(v_snd_58_);
lean_dec(v_snd_58_);
v___x_89_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0(v_fst_53_, v___x_84_, v___x_62_, v___x_86_, v___x_87_, v___x_88_);
lean_dec(v_fst_53_);
v___y_30_ = v___x_89_;
goto v___jp_29_;
}
v___jp_90_:
{
uint32_t v___x_91_; uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_91_ = 93;
v___x_92_ = lean_unbox_uint32(v_val_79_);
v___x_93_ = lean_uint32_dec_eq(v___x_92_, v___x_91_);
if (v___x_93_ == 0)
{
uint32_t v___x_94_; uint32_t v___x_95_; uint8_t v___x_96_; 
lean_del_object(v___x_81_);
lean_del_object(v___x_45_);
v___x_94_ = 91;
v___x_95_ = lean_unbox_uint32(v_val_79_);
v___x_96_ = lean_uint32_dec_eq(v___x_95_, v___x_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_26_, v_fst_49_);
if (lean_obj_tag(v___x_97_) == 1)
{
lean_object* v_val_98_; uint8_t v___x_99_; 
lean_dec_ref(v___x_84_);
lean_dec(v_val_79_);
v_val_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = lean_unbox(v_snd_58_);
lean_dec(v_snd_58_);
if (v___x_99_ == 0)
{
lean_object* v_snd_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_120_; 
v_snd_100_ = lean_ctor_get(v_val_98_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_val_98_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_val_98_, 0);
lean_dec(v_unused_121_);
v___x_102_ = v_val_98_;
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_100_);
lean_dec(v_val_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_fst_53_, v___x_104_);
lean_dec(v_fst_53_);
v___x_106_ = lean_box(v___x_64_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_106_);
lean_ctor_set(v___x_102_, 0, v_fst_57_);
v___x_108_ = v___x_102_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_fst_57_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_119_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_110_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_108_);
lean_ctor_set(v___x_60_, 0, v___x_105_);
v___x_110_ = v___x_60_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_118_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_110_);
lean_ctor_set(v___x_55_, 0, v_snd_100_);
v___x_112_ = v___x_55_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_snd_100_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_117_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_112_);
lean_ctor_set(v___x_51_, 0, v___x_62_);
v___x_114_ = v___x_51_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v_a_28_ = v___x_114_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec(v_val_98_);
lean_del_object(v___x_60_);
lean_dec(v_fst_57_);
lean_del_object(v___x_55_);
lean_dec(v_fst_53_);
lean_del_object(v___x_51_);
lean_dec(v_labelStart_27_);
return v___x_62_;
}
}
else
{
uint32_t v___x_122_; uint32_t v___x_123_; uint8_t v___x_124_; 
lean_dec(v___x_97_);
lean_del_object(v___x_60_);
lean_del_object(v___x_55_);
lean_del_object(v___x_51_);
v___x_122_ = 32;
v___x_123_ = lean_unbox_uint32(v_val_79_);
v___x_124_ = lean_uint32_dec_eq(v___x_123_, v___x_122_);
if (v___x_124_ == 0)
{
uint32_t v___x_125_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_125_ = 9;
v___x_126_ = lean_unbox_uint32(v_val_79_);
lean_dec(v_val_79_);
v___x_127_ = lean_uint32_dec_eq(v___x_126_, v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_snd_58_);
lean_dec(v_fst_57_);
v___x_128_ = lean_box(0);
v___x_129_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___lam__0(v_fst_53_, v___x_84_, v___x_62_, v___x_128_, v___x_64_, v_sawNonWs_83_);
lean_dec(v_fst_53_);
v___y_30_ = v___x_129_;
goto v___jp_29_;
}
else
{
goto v___jp_85_;
}
}
else
{
lean_dec(v_val_79_);
goto v___jp_85_;
}
}
}
else
{
lean_dec_ref(v___x_84_);
lean_dec(v_val_79_);
lean_del_object(v___x_60_);
lean_dec(v_snd_58_);
lean_dec(v_fst_57_);
lean_del_object(v___x_55_);
lean_dec(v_fst_53_);
lean_del_object(v___x_51_);
lean_dec(v_fst_49_);
lean_dec(v_labelStart_27_);
return v___x_62_;
}
}
else
{
uint8_t v___x_130_; 
lean_dec_ref(v___x_84_);
lean_dec(v_val_79_);
v___x_130_ = lean_unbox(v_fst_57_);
if (v___x_130_ == 0)
{
lean_del_object(v___x_81_);
lean_del_object(v___x_60_);
lean_dec(v_snd_58_);
lean_dec(v_fst_57_);
lean_del_object(v___x_55_);
lean_dec(v_fst_53_);
lean_del_object(v___x_51_);
lean_dec(v_fst_49_);
lean_del_object(v___x_45_);
lean_dec(v_labelStart_27_);
return v___x_62_;
}
else
{
lean_object* v_source_131_; lean_object* v_startPos_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v_source_131_ = lean_ctor_get(v_fst_49_, 0);
v_startPos_132_ = lean_ctor_get(v_fst_49_, 2);
lean_inc(v_startPos_132_);
v___x_133_ = l_Lean_Markdown_InlineSource_linesBetween(v_s_26_, v_source_131_, v_labelStart_27_, v_startPos_132_);
lean_inc(v_fst_49_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v_fst_49_);
lean_ctor_set(v___x_60_, 0, v___x_133_);
v___x_135_ = v___x_60_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_fst_49_);
v___x_135_ = v_reuseFailAlloc_150_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_135_);
v___x_137_ = v___x_81_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_149_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v_snd_58_);
lean_ctor_set(v___x_55_, 0, v_fst_57_);
v___x_139_ = v___x_55_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fst_57_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_snd_58_);
v___x_139_ = v_reuseFailAlloc_148_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_139_);
lean_ctor_set(v___x_51_, 0, v_fst_53_);
v___x_141_ = v___x_51_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_53_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_147_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_141_);
lean_ctor_set(v___x_45_, 0, v_fst_49_);
v___x_143_ = v___x_45_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_49_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_146_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_137_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
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
else
{
lean_object* v___x_170_; 
lean_dec(v___x_78_);
lean_dec(v_labelStart_27_);
if (v_isShared_61_ == 0)
{
v___x_170_ = v___x_60_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_57_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_snd_58_);
v___x_170_ = v_reuseFailAlloc_181_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_170_);
v___x_172_ = v___x_55_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_fst_53_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_180_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_172_);
v___x_174_ = v___x_51_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_fst_49_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_174_);
lean_ctor_set(v___x_45_, 0, v___x_62_);
v___x_176_ = v___x_45_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg___boxed(lean_object* v_s_189_, lean_object* v_labelStart_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg(v_s_189_, v_labelStart_190_, v_a_191_);
lean_dec_ref(v_s_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkLabel_x3f(lean_object* v_s_200_, lean_object* v_cur_201_){
_start:
{
lean_object* v_startPos_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_startPos_202_ = lean_ctor_get(v_cur_201_, 2);
lean_inc(v_startPos_202_);
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l_Lean_Markdown_parseLinkLabel_x3f___closed__1));
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_cur_201_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg(v_s_200_, v_startPos_202_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
return v___x_203_;
}
else
{
lean_object* v_val_208_; lean_object* v_fst_209_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_207_, 1);
v_fst_209_ = lean_ctor_get(v_val_208_, 0);
lean_inc(v_fst_209_);
lean_dec(v_val_208_);
if (lean_obj_tag(v_fst_209_) == 0)
{
return v___x_203_;
}
else
{
return v_fst_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkLabel_x3f___boxed(lean_object* v_s_210_, lean_object* v_cur_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Markdown_parseLinkLabel_x3f(v_s_210_, v_cur_211_);
lean_dec_ref(v_s_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0(lean_object* v_s_213_, lean_object* v_labelStart_214_, lean_object* v_inst_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___redArg(v_s_213_, v_labelStart_214_, v_a_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0___boxed(lean_object* v_s_218_, lean_object* v_labelStart_219_, lean_object* v_inst_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseLinkLabel_x3f_spec__0(v_s_218_, v_labelStart_219_, v_inst_220_, v_a_221_);
lean_dec_ref(v_s_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg(lean_object* v_s_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_271_; 
v_fst_225_ = lean_ctor_get(v_a_224_, 0);
v_snd_226_ = lean_ctor_get(v_a_224_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_224_);
if (v_isSharedCheck_271_ == 0)
{
v___x_228_ = v_a_224_;
v_isShared_229_ = v_isSharedCheck_271_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_snd_226_);
lean_inc(v_fst_225_);
lean_dec(v_a_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_271_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_223_, v_fst_225_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_268_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_268_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_268_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_268_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint32_t v___x_241_; uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_241_ = 32;
v___x_242_ = lean_unbox_uint32(v_val_237_);
v___x_243_ = lean_uint32_dec_eq(v___x_242_, v___x_241_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_244_ = 9;
v___x_245_ = lean_unbox_uint32(v_val_237_);
lean_dec(v_val_237_);
v___x_246_ = lean_uint32_dec_eq(v___x_245_, v___x_244_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_del_object(v___x_228_);
lean_inc(v_fst_225_);
v___x_247_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_223_, v_fst_225_);
if (lean_obj_tag(v___x_247_) == 1)
{
lean_object* v_val_248_; lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_262_; 
lean_del_object(v___x_239_);
lean_dec(v_fst_225_);
v_val_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_247_, 1);
v_snd_249_ = lean_ctor_get(v_val_248_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_val_248_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_val_248_, 0);
lean_dec(v_unused_263_);
v___x_251_ = v_val_248_;
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_dec(v_val_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_unsigned_to_nat(2u);
v___x_255_ = lean_nat_add(v_snd_226_, v___x_253_);
lean_dec(v_snd_226_);
v___x_256_ = lean_nat_dec_le(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_258_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_255_);
lean_ctor_set(v___x_251_, 0, v_snd_249_);
v___x_258_ = v___x_251_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_snd_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_255_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v_a_224_ = v___x_258_;
goto _start;
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v___x_255_);
lean_del_object(v___x_251_);
lean_dec(v_snd_249_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v___x_247_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_fst_225_);
lean_ctor_set(v___x_264_, 1, v_snd_226_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_264_);
v___x_266_ = v___x_239_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_del_object(v___x_239_);
goto v___jp_230_;
}
}
else
{
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
goto v___jp_230_;
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v___x_236_);
lean_del_object(v___x_228_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_fst_225_);
lean_ctor_set(v___x_269_, 1, v_snd_226_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = l_Lean_Markdown_InlineCursor_drop1(v_s_223_, v_fst_225_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_snd_226_);
v___x_233_ = v_reuseFailAlloc_235_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v_a_224_ = v___x_233_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg___boxed(lean_object* v_s_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg(v_s_272_, v_a_273_);
lean_dec_ref(v_s_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap(lean_object* v_s_275_, lean_object* v_cur_276_){
_start:
{
lean_object* v_endingsSeen_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_endingsSeen_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_cur_276_);
lean_ctor_set(v___x_278_, 1, v_endingsSeen_277_);
v___x_279_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg(v_s_275_, v___x_278_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_val_281_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_279_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v___x_279_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_fst_285_; lean_object* v___x_287_; 
v_fst_285_ = lean_ctor_get(v_val_281_, 0);
lean_inc(v_fst_285_);
lean_dec(v_val_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_fst_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_fst_285_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap___boxed(lean_object* v_s_290_, lean_object* v_cur_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap(v_s_290_, v_cur_291_);
lean_dec_ref(v_s_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0(lean_object* v_s_293_, lean_object* v_inst_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___redArg(v_s_293_, v_a_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0___boxed(lean_object* v_s_297_, lean_object* v_inst_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap_spec__0(v_s_297_, v_inst_298_, v_a_299_);
lean_dec_ref(v_s_297_);
return v_res_300_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
if (lean_obj_tag(v_x_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 1;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
else
{
if (lean_obj_tag(v_x_302_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
else
{
lean_object* v_val_306_; lean_object* v_val_307_; uint32_t v___x_308_; uint32_t v___x_309_; uint8_t v___x_310_; 
v_val_306_ = lean_ctor_get(v_x_301_, 0);
v_val_307_ = lean_ctor_get(v_x_302_, 0);
v___x_308_ = lean_unbox_uint32(v_val_306_);
v___x_309_ = lean_unbox_uint32(v_val_307_);
v___x_310_ = lean_uint32_dec_eq(v___x_308_, v___x_309_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(v_x_311_, v_x_312_);
lean_dec(v_x_312_);
lean_dec(v_x_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_315_; lean_object* v___x_316_; 
v___x_315_ = 32;
v___x_316_ = lean_box_uint32(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1;
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_319_; lean_object* v___x_320_; 
v___x_319_ = 9;
v___x_320_ = lean_box_uint32(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1;
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(lean_object* v_s_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_323_, v_a_324_);
v___x_329_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0);
v___x_330_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1);
v___x_332_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(v___x_328_, v___x_331_);
lean_dec(v___x_328_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_a_324_);
return v___x_333_;
}
else
{
goto v___jp_325_;
}
}
else
{
lean_dec(v___x_328_);
goto v___jp_325_;
}
v___jp_325_:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Markdown_InlineCursor_drop1(v_s_323_, v_a_324_);
v_a_324_ = v___x_326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___boxed(lean_object* v_s_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(v_s_334_, v_a_335_);
lean_dec_ref(v_s_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd(lean_object* v_s_337_, lean_object* v_cur_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(v_s_337_, v_cur_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
return v___x_339_;
}
else
{
lean_object* v_val_340_; uint8_t v___x_341_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
v___x_341_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_val_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_inc(v_val_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_342_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_337_, v_val_340_);
if (lean_obj_tag(v___x_342_) == 1)
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_snd_347_; lean_object* v___x_349_; 
v_snd_347_ = lean_ctor_get(v_val_343_, 1);
lean_inc(v_snd_347_);
lean_dec(v_val_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_snd_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_snd_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec(v___x_342_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
else
{
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd___boxed(lean_object* v_s_353_, lean_object* v_cur_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd(v_s_353_, v_cur_354_);
lean_dec_ref(v_s_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1(lean_object* v_s_356_, lean_object* v_inst_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(v_s_356_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___boxed(lean_object* v_s_360_, lean_object* v_inst_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1(v_s_360_, v_inst_361_, v_a_362_);
lean_dec_ref(v_s_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg(lean_object* v_s_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_386_; 
v_fst_366_ = lean_ctor_get(v_a_365_, 0);
v_snd_367_ = lean_ctor_get(v_a_365_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_386_ == 0)
{
v___x_369_ = v_a_365_;
v_isShared_370_ = v_isSharedCheck_386_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_367_);
lean_inc(v_fst_366_);
lean_dec(v_a_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_386_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_379_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_364_, v_snd_367_);
v___x_380_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0);
v___x_381_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1);
v___x_383_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__0(v___x_379_, v___x_382_);
lean_dec(v___x_379_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_del_object(v___x_369_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_fst_366_);
lean_ctor_set(v___x_384_, 1, v_snd_367_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_dec(v_fst_366_);
goto v___jp_371_;
}
}
else
{
lean_dec(v___x_379_);
lean_dec(v_fst_366_);
goto v___jp_371_;
}
v___jp_371_:
{
uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_372_ = 1;
v___x_373_ = l_Lean_Markdown_InlineCursor_drop1(v_s_364_, v_snd_367_);
v___x_374_ = lean_box(v___x_372_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_373_);
lean_ctor_set(v___x_369_, 0, v___x_374_);
v___x_376_ = v___x_369_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_373_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_a_365_ = v___x_376_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg___boxed(lean_object* v_s_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg(v_s_387_, v_a_388_);
lean_dec_ref(v_s_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f(lean_object* v_s_390_, lean_object* v_cur_391_){
_start:
{
lean_object* v_openerR_393_; uint8_t v_sawWs_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_sawWs_415_ = 0;
v___x_416_ = lean_box(v_sawWs_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_cur_391_);
v___x_418_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg(v_s_390_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_423_; 
v_val_420_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v___x_418_, 1);
v_fst_421_ = lean_ctor_get(v_val_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v_val_420_, 1);
lean_inc_n(v_snd_422_, 2);
lean_dec(v_val_420_);
v___x_423_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_390_, v_snd_422_);
if (lean_obj_tag(v___x_423_) == 1)
{
lean_object* v_val_424_; lean_object* v_snd_425_; lean_object* v___x_426_; 
lean_dec(v_snd_422_);
lean_dec(v_fst_421_);
v_val_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v___x_423_, 1);
v_snd_425_ = lean_ctor_get(v_val_424_, 1);
lean_inc(v_snd_425_);
lean_dec(v_val_424_);
v___x_426_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg(v_s_390_, v_snd_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(0);
return v___x_427_;
}
else
{
lean_object* v_val_428_; 
v_val_428_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_426_, 1);
v_openerR_393_ = v_val_428_;
goto v___jp_392_;
}
}
else
{
uint8_t v___x_429_; 
lean_dec(v___x_423_);
v___x_429_ = lean_unbox(v_fst_421_);
lean_dec(v_fst_421_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_snd_422_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
v_openerR_393_ = v_snd_422_;
goto v___jp_392_;
}
}
}
v___jp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Markdown_parseLinkTitle_x3f(v_s_390_, v_openerR_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_414_; 
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_394_, 1);
v_fst_396_ = lean_ctor_get(v_val_395_, 0);
v_snd_397_ = lean_ctor_get(v_val_395_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_val_395_);
if (v_isSharedCheck_414_ == 0)
{
v___x_399_ = v_val_395_;
v_isShared_400_ = v_isSharedCheck_414_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_val_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_414_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd(v_s_390_, v_snd_397_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_402_; 
lean_del_object(v___x_399_);
lean_dec(v_fst_396_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
v_val_403_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_413_ == 0)
{
v___x_405_ = v___x_401_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_val_403_);
lean_dec(v___x_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v_val_403_);
v___x_408_ = v___x_399_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fst_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_val_403_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f___boxed(lean_object* v_s_431_, lean_object* v_cur_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f(v_s_431_, v_cur_432_);
lean_dec_ref(v_s_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0(lean_object* v_s_434_, lean_object* v_inst_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___redArg(v_s_434_, v_a_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0___boxed(lean_object* v_s_438_, lean_object* v_inst_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f_spec__0(v_s_438_, v_inst_439_, v_a_440_);
lean_dec_ref(v_s_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkRefDef_x3f(lean_object* v_s_442_, lean_object* v_source_443_, lean_object* v_start_444_){
_start:
{
lean_object* v___x_445_; lean_object* v_cur_446_; uint32_t v___x_447_; lean_object* v___x_448_; 
v___x_445_ = l_Lean_Markdown_InlineSource_stopPos___redArg(v_source_443_);
v_cur_446_ = l_Lean_Markdown_InlineSource_cursor___redArg(v_source_443_, v_start_444_, v___x_445_);
v___x_447_ = 91;
v___x_448_ = l_Lean_Markdown_InlineCursor_parseChar_x3f(v_s_442_, v___x_447_, v_cur_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(0);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v_fst_451_; lean_object* v_snd_452_; lean_object* v___x_453_; 
v_val_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_448_, 1);
v_fst_451_ = lean_ctor_get(v_val_450_, 0);
lean_inc(v_fst_451_);
v_snd_452_ = lean_ctor_get(v_val_450_, 1);
lean_inc(v_snd_452_);
lean_dec(v_val_450_);
v___x_453_ = l_Lean_Markdown_parseLinkLabel_x3f(v_s_442_, v_snd_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_454_; 
lean_dec(v_fst_451_);
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
lean_object* v_val_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; uint32_t v___x_458_; lean_object* v___x_459_; 
v_val_455_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v___x_453_, 1);
v_fst_456_ = lean_ctor_get(v_val_455_, 0);
lean_inc(v_fst_456_);
v_snd_457_ = lean_ctor_get(v_val_455_, 1);
lean_inc(v_snd_457_);
lean_dec(v_val_455_);
v___x_458_ = 93;
v___x_459_ = l_Lean_Markdown_InlineCursor_parseChar_x3f(v_s_442_, v___x_458_, v_snd_457_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_460_; 
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_val_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; uint32_t v___x_464_; lean_object* v___x_465_; 
v_val_461_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_459_, 1);
v_fst_462_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v_val_461_, 1);
lean_inc(v_snd_463_);
lean_dec(v_val_461_);
v___x_464_ = 58;
v___x_465_ = l_Lean_Markdown_InlineCursor_parseChar_x3f(v_s_442_, v___x_464_, v_snd_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
lean_dec(v_fst_462_);
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
else
{
lean_object* v_val_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_470_; 
v_val_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_465_, 1);
v_fst_468_ = lean_ctor_get(v_val_467_, 0);
lean_inc(v_fst_468_);
v_snd_469_ = lean_ctor_get(v_val_467_, 1);
lean_inc(v_snd_469_);
lean_dec(v_val_467_);
v___x_470_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_skipRefDefDestGap(v_s_442_, v_snd_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_471_; 
lean_dec(v_fst_468_);
lean_dec(v_fst_462_);
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_471_ = lean_box(0);
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
v_val_472_ = lean_ctor_get(v___x_470_, 0);
lean_inc_n(v_val_472_, 2);
lean_dec_ref_known(v___x_470_, 1);
v___x_473_ = l_Lean_Markdown_parseLinkDestination_x3f(v_s_442_, v_val_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; 
lean_dec(v_val_472_);
lean_dec(v_fst_468_);
lean_dec(v_fst_462_);
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_517_; 
v_val_475_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_517_ == 0)
{
v___x_477_ = v___x_473_;
v_isShared_478_ = v_isSharedCheck_517_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_val_475_);
lean_dec(v___x_473_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_517_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_516_; 
v_fst_479_ = lean_ctor_get(v_val_475_, 0);
v_snd_480_ = lean_ctor_get(v_val_475_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_val_475_);
if (v_isSharedCheck_516_ == 0)
{
v___x_482_ = v_val_475_;
v_isShared_483_ = v_isSharedCheck_516_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snd_480_);
lean_inc(v_fst_479_);
lean_dec(v_val_475_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_516_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v_angles_x3f_511_; 
v_angles_x3f_511_ = lean_ctor_get(v_fst_479_, 0);
if (lean_obj_tag(v_angles_x3f_511_) == 0)
{
lean_object* v_startPos_512_; lean_object* v_startPos_513_; uint8_t v_decide_514_; 
v_startPos_512_ = lean_ctor_get(v_snd_480_, 2);
v_startPos_513_ = lean_ctor_get(v_val_472_, 2);
lean_inc(v_startPos_513_);
lean_dec(v_val_472_);
v_decide_514_ = lean_nat_dec_eq(v_startPos_512_, v_startPos_513_);
lean_dec(v_startPos_513_);
if (v_decide_514_ == 0)
{
goto v___jp_495_;
}
else
{
lean_object* v___x_515_; 
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
lean_dec(v_fst_479_);
lean_del_object(v___x_477_);
lean_dec(v_fst_468_);
lean_dec(v_fst_462_);
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
else
{
lean_dec(v_val_472_);
goto v___jp_495_;
}
v___jp_484_:
{
lean_object* v_startPos_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v_startPos_487_ = lean_ctor_get(v_snd_486_, 2);
lean_inc(v_startPos_487_);
lean_dec_ref(v_snd_486_);
v___x_488_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_488_, 0, v_fst_451_);
lean_ctor_set(v___x_488_, 1, v_fst_456_);
lean_ctor_set(v___x_488_, 2, v_fst_462_);
lean_ctor_set(v___x_488_, 3, v_fst_468_);
lean_ctor_set(v___x_488_, 4, v_fst_479_);
lean_ctor_set(v___x_488_, 5, v_fst_485_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v_startPos_487_);
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_startPos_487_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_490_);
v___x_492_ = v___x_477_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
v___jp_495_:
{
lean_object* v___x_496_; 
lean_inc(v_snd_480_);
v___x_496_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_parseRefDefTitle_x3f(v_s_442_, v_snd_480_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd(v_s_442_, v_snd_480_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; 
lean_del_object(v___x_482_);
lean_dec(v_fst_479_);
lean_del_object(v___x_477_);
lean_dec(v_fst_468_);
lean_dec(v_fst_462_);
lean_dec(v_fst_456_);
lean_dec(v_fst_451_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_500_; 
v_val_499_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v___x_497_, 1);
v___x_500_ = lean_box(0);
v_fst_485_ = v___x_500_;
v_snd_486_ = v_val_499_;
goto v___jp_484_;
}
}
else
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_snd_480_);
v_val_501_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v___x_496_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v___x_496_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; 
v_fst_505_ = lean_ctor_get(v_val_501_, 0);
lean_inc(v_fst_505_);
v_snd_506_ = lean_ctor_get(v_val_501_, 1);
lean_inc(v_snd_506_);
lean_dec(v_val_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_fst_505_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_fst_505_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v_fst_485_ = v___x_508_;
v_snd_486_ = v_snd_506_;
goto v___jp_484_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseLinkRefDef_x3f___boxed(lean_object* v_s_518_, lean_object* v_source_519_, lean_object* v_start_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Markdown_parseLinkRefDef_x3f(v_s_518_, v_source_519_, v_start_520_);
lean_dec_ref(v_s_518_);
return v_res_521_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
if (lean_obj_tag(v_x_523_) == 0)
{
uint8_t v___x_524_; 
v___x_524_ = 1;
return v___x_524_;
}
else
{
uint8_t v___x_525_; 
v___x_525_ = 0;
return v___x_525_;
}
}
else
{
if (lean_obj_tag(v_x_523_) == 0)
{
uint8_t v___x_526_; 
v___x_526_ = 0;
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v_val_528_; uint8_t v_decide_529_; 
v_val_527_ = lean_ctor_get(v_x_522_, 0);
v_val_528_ = lean_ctor_get(v_x_523_, 0);
v_decide_529_ = lean_nat_dec_eq(v_val_527_, v_val_528_);
return v_decide_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg(v_x_530_, v_x_531_);
lean_dec(v_x_531_);
lean_dec(v_x_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0(lean_object* v_s_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg(v_x_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___boxed(lean_object* v_s_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0(v_s_538_, v_x_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec(v_x_539_);
lean_dec_ref(v_s_538_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1(lean_object* v_p_543_, lean_object* v_s_544_, lean_object* v_as_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_b_548_){
_start:
{
lean_object* v_a_550_; uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_554_ == 0)
{
lean_dec(v_p_543_);
return v_b_548_;
}
else
{
lean_object* v_a_555_; lean_object* v_startInclusive_556_; lean_object* v_endExclusive_557_; uint8_t v___x_558_; 
v_a_555_ = lean_array_uget_borrowed(v_as_545_, v_i_547_);
v_startInclusive_556_ = lean_ctor_get(v_a_555_, 0);
v_endExclusive_557_ = lean_ctor_get(v_a_555_, 1);
v___x_558_ = lean_nat_dec_le(v_endExclusive_557_, v_p_543_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_startInclusive_556_, v___x_559_);
v___x_561_ = lean_nat_dec_le(v___x_560_, v_p_543_);
lean_dec(v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_inc(v_a_555_);
v___x_562_ = lean_array_push(v_b_548_, v_a_555_);
v_a_550_ = v___x_562_;
goto v___jp_549_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
lean_inc_n(v_endExclusive_557_, 2);
lean_inc(v_p_543_);
v___x_563_ = l_Lean_Markdown_subsliceClamped___redArg(v_p_543_, v_endExclusive_557_);
v___x_564_ = l_Lean_Markdown_parseLineEnding_x3f(v_s_544_, v___x_563_, v_p_543_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_endExclusive_557_);
v___x_566_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__0___redArg(v___x_564_, v___x_565_);
lean_dec_ref_known(v___x_565_, 1);
lean_dec(v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_array_push(v_b_548_, v___x_563_);
v_a_550_ = v___x_567_;
goto v___jp_549_;
}
else
{
lean_dec_ref(v___x_563_);
v_a_550_ = v_b_548_;
goto v___jp_549_;
}
}
}
else
{
v_a_550_ = v_b_548_;
goto v___jp_549_;
}
}
v___jp_549_:
{
size_t v___x_551_; size_t v___x_552_; 
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_547_, v___x_551_);
v_i_547_ = v___x_552_;
v_b_548_ = v_a_550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1___boxed(lean_object* v_p_568_, lean_object* v_s_569_, lean_object* v_as_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_b_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_575_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1(v_p_568_, v_s_569_, v_as_570_, v_sz_boxed_574_, v_i_boxed_575_, v_b_573_);
lean_dec_ref(v_as_570_);
lean_dec_ref(v_s_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f(lean_object* v_s_579_, lean_object* v_source_580_, lean_object* v_p_581_){
_start:
{
lean_object* v___x_582_; lean_object* v_kept_583_; size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v_kept_583_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___closed__0));
v_sz_584_ = lean_array_size(v_source_580_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f_spec__1(v_p_581_, v_s_579_, v_source_580_, v_sz_584_, v___x_585_, v_kept_583_);
v___x_587_ = lean_array_get_size(v___x_586_);
v___x_588_ = lean_nat_dec_lt(v___x_582_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v___x_586_);
v___x_589_ = lean_box(0);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = l_Lean_Markdown_InlineSource_ofLines(v_s_579_, v___x_586_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f___boxed(lean_object* v_s_592_, lean_object* v_source_593_, lean_object* v_p_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f(v_s_592_, v_source_593_, v_p_594_);
lean_dec_ref(v_source_593_);
lean_dec_ref(v_s_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg(lean_object* v_s_596_, lean_object* v_source_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_snd_599_; lean_object* v_fst_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_648_; 
v_snd_599_ = lean_ctor_get(v_a_598_, 1);
v_fst_600_ = lean_ctor_get(v_a_598_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_648_ == 0)
{
v___x_602_ = v_a_598_;
v_isShared_603_ = v_isSharedCheck_648_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_600_);
lean_dec(v_a_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_648_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_647_; 
v_fst_604_ = lean_ctor_get(v_snd_599_, 0);
v_snd_605_ = lean_ctor_get(v_snd_599_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_snd_599_);
if (v_isSharedCheck_647_ == 0)
{
v___x_607_ = v_snd_599_;
v_isShared_608_ = v_isSharedCheck_647_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_snd_599_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_647_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_616_; 
v___x_616_ = lean_unbox(v_snd_605_);
if (v___x_616_ == 0)
{
lean_dec_ref(v_source_597_);
goto v___jp_609_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_617_ = l_Lean_Markdown_InlineSource_stopPos___redArg(v_source_597_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_fst_604_, v___x_618_);
v___x_620_ = lean_nat_dec_le(v___x_619_, v___x_617_);
lean_dec(v___x_617_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_source_597_);
goto v___jp_609_;
}
else
{
lean_object* v___x_621_; 
lean_del_object(v___x_607_);
lean_del_object(v___x_602_);
lean_inc(v_fst_604_);
lean_inc_ref(v_source_597_);
v___x_621_ = l_Lean_Markdown_parseLinkRefDef_x3f(v_s_596_, v_source_597_, v_fst_604_);
if (lean_obj_tag(v___x_621_) == 0)
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_snd_605_);
v___x_622_ = 0;
v___x_623_ = lean_box(v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_fst_604_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_fst_600_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v_a_598_ = v___x_625_;
goto _start;
}
else
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_fst_604_);
v_val_627_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_646_ == 0)
{
v___x_629_ = v___x_621_;
v_isShared_630_ = v_isSharedCheck_646_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v___x_621_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_646_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_645_; 
v_fst_631_ = lean_ctor_get(v_val_627_, 0);
v_snd_632_ = lean_ctor_get(v_val_627_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_val_627_);
if (v_isSharedCheck_645_ == 0)
{
v___x_634_ = v_val_627_;
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snd_632_);
lean_inc(v_fst_631_);
lean_dec(v_val_627_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 9);
lean_ctor_set(v___x_629_, 0, v_fst_631_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_631_);
v___x_637_ = v_reuseFailAlloc_644_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_array_push(v_fst_600_, v___x_637_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_snd_605_);
lean_ctor_set(v___x_634_, 0, v_snd_632_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_snd_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_605_);
v___x_640_ = v_reuseFailAlloc_643_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v_a_598_ = v___x_641_;
goto _start;
}
}
}
}
}
}
}
v___jp_609_:
{
lean_object* v___x_611_; 
if (v_isShared_608_ == 0)
{
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_snd_605_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_611_);
v___x_613_ = v___x_602_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg___boxed(lean_object* v_s_649_, lean_object* v_source_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg(v_s_649_, v_source_650_, v_a_651_);
lean_dec_ref(v_s_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extractRefDefs(lean_object* v_s_655_, lean_object* v_source_656_){
_start:
{
lean_object* v___x_657_; lean_object* v_defs_658_; lean_object* v_p_659_; uint8_t v_keep_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_686_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v_defs_658_ = ((lean_object*)(l_Lean_Markdown_extractRefDefs___closed__0));
v_p_659_ = l_Lean_Markdown_InlineSource_startPos___redArg(v_source_656_);
v_keep_660_ = 1;
v___x_661_ = lean_box(v_keep_660_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_p_659_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_defs_658_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_inc_ref(v_source_656_);
v___x_664_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg(v_s_655_, v_source_656_, v___x_663_);
v_fst_665_ = lean_ctor_get(v___x_664_, 0);
v_snd_666_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_686_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snd_666_);
lean_inc(v_fst_665_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_array_get_size(v_fst_665_);
v___x_671_ = lean_nat_dec_eq(v___x_670_, v___x_657_);
if (v___x_671_ == 0)
{
lean_object* v_fst_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_del_object(v___x_668_);
v_fst_672_ = lean_ctor_get(v_snd_666_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_snd_666_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_snd_666_, 1);
lean_dec(v_unused_681_);
v___x_674_ = v_snd_666_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_fst_672_);
lean_dec(v_snd_666_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = l___private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_sourceFrom_x3f(v_s_655_, v_source_656_, v_fst_672_);
lean_dec_ref(v_source_656_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_676_);
lean_ctor_set(v___x_674_, 0, v_fst_665_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v_snd_666_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_source_656_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_682_);
v___x_684_ = v___x_668_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_extractRefDefs___boxed(lean_object* v_s_687_, lean_object* v_source_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Markdown_extractRefDefs(v_s_687_, v_source_688_);
lean_dec_ref(v_s_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0(lean_object* v_s_690_, lean_object* v_source_691_, lean_object* v_inst_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___redArg(v_s_690_, v_source_691_, v_a_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0___boxed(lean_object* v_s_695_, lean_object* v_source_696_, lean_object* v_inst_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_extractRefDefs_spec__0(v_s_695_, v_source_696_, v_inst_697_, v_a_698_);
lean_dec_ref(v_s_695_);
return v_res_699_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_LinkSyntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_RefDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_LinkSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__0___boxed__const__1);
l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_RefDef_0__Lean_Markdown_consumeRefDefLineEnd_spec__1___redArg___closed__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_RefDef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_LinkSyntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_RefDef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_LinkSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_RefDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_RefDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_RefDef(builtin);
}
#ifdef __cplusplus
}
#endif
