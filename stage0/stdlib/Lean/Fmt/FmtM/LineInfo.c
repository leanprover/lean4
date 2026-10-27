// Lean compiler output
// Module: Lean.Fmt.FmtM.LineInfo
// Imports: public import Lean.Fmt.FmtM.Error import Init.While import Init.Data.Slice import Lean.Fmt.Util.Basic public import Lean.Syntax
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object*);
lean_object* l_Lean_Syntax_getStartPos_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_collectLineInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__0 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_collectLineInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__1 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_collectLineInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_collectLineInfos___closed__1_value)}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__2 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_collectLineInfos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_collectLineInfos___closed__2_value)}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__3 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_collectLineInfos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_collectLineInfos___closed__3_value)}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__4 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_collectLineInfos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_collectLineInfos___closed__0_value),((lean_object*)&l_Lean_Fmt_collectLineInfos___closed__4_value)}};
static const lean_object* l_Lean_Fmt_collectLineInfos___closed__5 = (const lean_object*)&l_Lean_Fmt_collectLineInfos___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0_value;
static const lean_array_object l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__1 = (const lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0_value),((lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__2 = (const lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default = (const lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo = (const lean_object*)&l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__2_value;
static const lean_string_object l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " - "};
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__1_value;
static const lean_string_object l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "; #"};
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__2 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__2_value;
static const lean_string_object l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "; i"};
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__3 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__3_value;
static const lean_string_object l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__4 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringSyntaxLineInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo = (const lean_object*)&l_Lean_Fmt_instToStringSyntaxLineInfo___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_collectSyntaxLineInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_collectSyntaxLineInfos___closed__0 = (const lean_object*)&l_Lean_Fmt_collectSyntaxLineInfos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo_default(lean_object* v_s_1_){
_start:
{
lean_object* v_startInclusive_2_; lean_object* v_endExclusive_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_13_; 
v_startInclusive_2_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_3_ = lean_ctor_get(v_s_1_, 2);
v_isSharedCheck_13_ = !lean_is_exclusive(v_s_1_);
if (v_isSharedCheck_13_ == 0)
{
lean_object* v_unused_14_; 
v_unused_14_ = lean_ctor_get(v_s_1_, 0);
lean_dec(v_unused_14_);
v___x_5_ = v_s_1_;
v_isShared_6_ = v_isSharedCheck_13_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_endExclusive_3_);
lean_inc(v_startInclusive_2_);
lean_dec(v_s_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_13_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_sub(v_endExclusive_3_, v_startInclusive_2_);
lean_dec(v_startInclusive_2_);
lean_dec(v_endExclusive_3_);
lean_inc(v___x_8_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 2, v___x_9_);
lean_ctor_set(v___x_5_, 1, v___x_7_);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_11_ = v___x_5_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_12_, 2, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo(lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Fmt_instInhabitedLineInfo_default(v_a_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(lean_object* v___x_17_, lean_object* v_____r_18_, lean_object* v_r_19_, lean_object* v_lineLength_20_, lean_object* v_lineIndentation_21_, uint8_t v_foundNonSpaceChar_22_, lean_object* v_lineStartPos_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v_lineStartPos_23_);
lean_ctor_set(v___x_24_, 1, v___x_17_);
v___x_25_ = lean_box(v_foundNonSpaceChar_22_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v_lineIndentation_21_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_lineLength_20_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v_r_19_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0___boxed(lean_object* v___x_31_, lean_object* v_____r_32_, lean_object* v_r_33_, lean_object* v_lineLength_34_, lean_object* v_lineIndentation_35_, lean_object* v_foundNonSpaceChar_36_, lean_object* v_lineStartPos_37_){
_start:
{
uint8_t v_foundNonSpaceChar_boxed_38_; lean_object* v_res_39_; 
v_foundNonSpaceChar_boxed_38_ = lean_unbox(v_foundNonSpaceChar_36_);
v_res_39_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_31_, v_____r_32_, v_r_33_, v_lineLength_34_, v_lineIndentation_35_, v_foundNonSpaceChar_boxed_38_, v_lineStartPos_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(lean_object* v_s_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___y_43_; lean_object* v_snd_47_; lean_object* v_snd_48_; lean_object* v_snd_49_; lean_object* v_snd_50_; lean_object* v_fst_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_126_; 
v_snd_47_ = lean_ctor_get(v_a_41_, 1);
lean_inc(v_snd_47_);
v_snd_48_ = lean_ctor_get(v_snd_47_, 1);
lean_inc(v_snd_48_);
v_snd_49_ = lean_ctor_get(v_snd_48_, 1);
lean_inc(v_snd_49_);
v_snd_50_ = lean_ctor_get(v_snd_49_, 1);
lean_inc(v_snd_50_);
v_fst_51_ = lean_ctor_get(v_a_41_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_a_41_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v_a_41_, 1);
lean_dec(v_unused_127_);
v___x_53_ = v_a_41_;
v_isShared_54_ = v_isSharedCheck_126_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_fst_51_);
lean_dec(v_a_41_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_126_;
goto v_resetjp_52_;
}
v___jp_42_:
{
if (lean_obj_tag(v___y_43_) == 0)
{
lean_object* v_a_44_; 
v_a_44_ = lean_ctor_get(v___y_43_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v___y_43_, 1);
return v_a_44_;
}
else
{
lean_object* v_a_45_; 
v_a_45_ = lean_ctor_get(v___y_43_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___y_43_, 1);
v_a_41_ = v_a_45_;
goto _start;
}
}
v_resetjp_52_:
{
lean_object* v_fst_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_124_; 
v_fst_55_ = lean_ctor_get(v_snd_47_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_snd_47_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; 
v_unused_125_ = lean_ctor_get(v_snd_47_, 1);
lean_dec(v_unused_125_);
v___x_57_ = v_snd_47_;
v_isShared_58_ = v_isSharedCheck_124_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_fst_55_);
lean_dec(v_snd_47_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_124_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_fst_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_122_; 
v_fst_59_ = lean_ctor_get(v_snd_48_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_snd_48_);
if (v_isSharedCheck_122_ == 0)
{
lean_object* v_unused_123_; 
v_unused_123_ = lean_ctor_get(v_snd_48_, 1);
lean_dec(v_unused_123_);
v___x_61_ = v_snd_48_;
v_isShared_62_ = v_isSharedCheck_122_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_fst_59_);
lean_dec(v_snd_48_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_122_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_fst_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_120_; 
v_fst_63_ = lean_ctor_get(v_snd_49_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_snd_49_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_snd_49_, 1);
lean_dec(v_unused_121_);
v___x_65_ = v_snd_49_;
v_isShared_66_ = v_isSharedCheck_120_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_fst_63_);
lean_dec(v_snd_49_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_120_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_119_; 
v_fst_67_ = lean_ctor_get(v_snd_50_, 0);
v_snd_68_ = lean_ctor_get(v_snd_50_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_snd_50_);
if (v_isSharedCheck_119_ == 0)
{
v___x_70_ = v_snd_50_;
v_isShared_71_ = v_isSharedCheck_119_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snd_68_);
lean_inc(v_fst_67_);
lean_dec(v_snd_50_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_119_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_str_72_; lean_object* v_startInclusive_73_; lean_object* v_endExclusive_74_; lean_object* v___x_75_; uint8_t v_decide_76_; 
v_str_72_ = lean_ctor_get(v_s_40_, 0);
v_startInclusive_73_ = lean_ctor_get(v_s_40_, 1);
v_endExclusive_74_ = lean_ctor_get(v_s_40_, 2);
v___x_75_ = lean_nat_sub(v_endExclusive_74_, v_startInclusive_73_);
v_decide_76_ = lean_nat_dec_eq(v_snd_68_, v___x_75_);
lean_dec(v___x_75_);
if (v_decide_76_ == 0)
{
lean_object* v_lineLength_77_; uint8_t v___x_78_; lean_object* v___x_79_; uint32_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint32_t v___x_95_; uint8_t v___x_96_; 
lean_del_object(v___x_70_);
lean_del_object(v___x_65_);
lean_del_object(v___x_61_);
lean_del_object(v___x_57_);
lean_del_object(v___x_53_);
v_lineLength_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = 1;
v___x_79_ = lean_nat_add(v_startInclusive_73_, v_snd_68_);
v___x_80_ = lean_string_utf8_get_fast(v_str_72_, v___x_79_);
v___x_81_ = lean_string_utf8_next_fast(v_str_72_, v___x_79_);
lean_dec(v___x_79_);
v___x_82_ = lean_nat_sub(v___x_81_, v_startInclusive_73_);
v___x_95_ = 32;
v___x_96_ = lean_uint32_dec_eq(v___x_80_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_fst_63_);
goto v___jp_83_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_unbox(v_fst_63_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; 
lean_dec(v_snd_68_);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_fst_55_, v___x_98_);
lean_dec(v_fst_55_);
v___x_100_ = lean_nat_add(v_fst_59_, v___x_98_);
lean_dec(v_fst_59_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_unbox(v_fst_63_);
lean_dec(v_fst_63_);
v___x_103_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_82_, v___x_101_, v_fst_51_, v___x_99_, v___x_100_, v___x_102_, v_fst_67_);
v___y_43_ = v___x_103_;
goto v___jp_42_;
}
else
{
lean_dec(v_fst_63_);
goto v___jp_83_;
}
}
v___jp_83_:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 10;
v___x_85_ = lean_uint32_dec_eq(v___x_80_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_snd_68_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_fst_55_, v___x_86_);
lean_dec(v_fst_55_);
v___x_88_ = lean_box(0);
v___x_89_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_82_, v___x_88_, v_fst_51_, v___x_87_, v_fst_59_, v___x_78_, v_fst_67_);
v___y_43_ = v___x_89_;
goto v___jp_42_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = l_String_Slice_subslice_x21(v_s_40_, v_fst_67_, v_snd_68_);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v_fst_55_);
lean_ctor_set(v___x_91_, 1, v_fst_59_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
v___x_92_ = lean_array_push(v_fst_51_, v___x_91_);
v___x_93_ = lean_box(0);
lean_inc(v___x_82_);
v___x_94_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_82_, v___x_93_, v___x_92_, v_lineLength_77_, v_lineLength_77_, v_decide_76_, v___x_82_);
v___y_43_ = v___x_94_;
goto v___jp_42_;
}
}
}
else
{
lean_object* v___x_105_; 
if (v_isShared_71_ == 0)
{
v___x_105_ = v___x_70_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_fst_67_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_snd_68_);
v___x_105_ = v_reuseFailAlloc_118_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_107_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_105_);
v___x_107_ = v___x_65_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_fst_63_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_105_);
v___x_107_ = v_reuseFailAlloc_117_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_107_);
v___x_109_ = v___x_61_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_fst_59_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_116_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_109_);
v___x_111_ = v___x_57_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_fst_55_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_115_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_111_);
v___x_113_ = v___x_53_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_fst_51_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___boxed(lean_object* v_s_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_128_, v_a_129_);
lean_dec_ref(v_s_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos(lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_snd_151_; lean_object* v_snd_152_; lean_object* v_snd_153_; lean_object* v_snd_154_; lean_object* v_fst_155_; lean_object* v_fst_156_; lean_object* v_fst_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_149_ = ((lean_object*)(l_Lean_Fmt_collectLineInfos___closed__5));
v___x_150_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_148_, v___x_149_);
v_snd_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_snd_151_);
v_snd_152_ = lean_ctor_get(v_snd_151_, 1);
lean_inc(v_snd_152_);
v_snd_153_ = lean_ctor_get(v_snd_152_, 1);
v_snd_154_ = lean_ctor_get(v_snd_153_, 1);
lean_inc(v_snd_154_);
v_fst_155_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_155_);
lean_dec_ref(v___x_150_);
v_fst_156_ = lean_ctor_get(v_snd_151_, 0);
lean_inc(v_fst_156_);
lean_dec(v_snd_151_);
v_fst_157_ = lean_ctor_get(v_snd_152_, 0);
lean_inc(v_fst_157_);
lean_dec(v_snd_152_);
v_fst_158_ = lean_ctor_get(v_snd_154_, 0);
lean_inc(v_fst_158_);
v_snd_159_ = lean_ctor_get(v_snd_154_, 1);
lean_inc(v_snd_159_);
lean_dec(v_snd_154_);
v___x_160_ = l_String_Slice_subslice_x21(v_s_148_, v_fst_158_, v_snd_159_);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v_fst_156_);
lean_ctor_set(v___x_161_, 1, v_fst_157_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
v___x_162_ = lean_array_push(v_fst_155_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos___boxed(lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Fmt_collectLineInfos(v_s_163_);
lean_dec_ref(v_s_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0(lean_object* v_s_165_, lean_object* v_inst_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_165_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___boxed(lean_object* v_s_169_, lean_object* v_inst_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0(v_s_169_, v_inst_170_, v_a_171_);
lean_dec_ref(v_s_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0(lean_object* v_li_187_){
_start:
{
lean_object* v_length_188_; lean_object* v_indentation_189_; lean_object* v_line_190_; lean_object* v_startPos_191_; lean_object* v_endPos_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_length_188_ = lean_ctor_get(v_li_187_, 0);
lean_inc(v_length_188_);
v_indentation_189_ = lean_ctor_get(v_li_187_, 1);
lean_inc(v_indentation_189_);
v_line_190_ = lean_ctor_get(v_li_187_, 2);
lean_inc_ref(v_line_190_);
v_startPos_191_ = lean_ctor_get(v_li_187_, 4);
lean_inc(v_startPos_191_);
v_endPos_192_ = lean_ctor_get(v_li_187_, 5);
lean_inc(v_endPos_192_);
lean_dec_ref(v_li_187_);
v___x_193_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__0));
v___x_194_ = lean_string_append(v_line_190_, v___x_193_);
v___x_195_ = l_Nat_reprFast(v_startPos_191_);
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__1));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
v___x_199_ = l_Nat_reprFast(v_endPos_192_);
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__2));
v___x_202_ = lean_string_append(v___x_200_, v___x_201_);
v___x_203_ = l_Nat_reprFast(v_length_188_);
v___x_204_ = lean_string_append(v___x_202_, v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__3));
v___x_206_ = lean_string_append(v___x_204_, v___x_205_);
v___x_207_ = l_Nat_reprFast(v_indentation_189_);
v___x_208_ = lean_string_append(v___x_206_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__4));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(lean_object* v_s_213_, lean_object* v___y_214_, uint8_t v___y_215_, lean_object* v_a_216_, lean_object* v_b_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_array_219_; lean_object* v_start_220_; lean_object* v_stop_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_257_; 
v_array_219_ = lean_ctor_get(v_a_216_, 0);
v_start_220_ = lean_ctor_get(v_a_216_, 1);
v_stop_221_ = lean_ctor_get(v_a_216_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_257_ == 0)
{
v___x_223_ = v_a_216_;
v_isShared_224_ = v_isSharedCheck_257_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_stop_221_);
lean_inc(v_start_220_);
lean_inc(v_array_219_);
lean_dec(v_a_216_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_257_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_lt(v_start_220_, v_stop_221_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_del_object(v___x_223_);
lean_dec(v_stop_221_);
lean_dec(v_start_220_);
lean_dec_ref(v_array_219_);
lean_dec_ref(v___y_214_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_b_217_);
lean_ctor_set(v___x_226_, 1, v___y_218_);
return v___x_226_;
}
else
{
lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_256_; 
v_fst_227_ = lean_ctor_get(v_b_217_, 0);
v_snd_228_ = lean_ctor_get(v_b_217_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_b_217_);
if (v_isSharedCheck_256_ == 0)
{
v___x_230_ = v_b_217_;
v_isShared_231_ = v_isSharedCheck_256_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_b_217_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_256_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_range_233_; lean_object* v_length_234_; lean_object* v_indentation_235_; lean_object* v_startInclusive_236_; lean_object* v_endExclusive_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_232_ = lean_array_fget_borrowed(v_array_219_, v_start_220_);
v_range_233_ = lean_ctor_get(v___x_232_, 2);
v_length_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_length_234_);
v_indentation_235_ = lean_ctor_get(v___x_232_, 1);
lean_inc(v_indentation_235_);
v_startInclusive_236_ = lean_ctor_get(v_range_233_, 0);
lean_inc(v_startInclusive_236_);
v_endExclusive_237_ = lean_ctor_get(v_range_233_, 1);
lean_inc(v_endExclusive_237_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_start_220_, v___x_238_);
lean_dec(v_start_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_239_);
v___x_241_ = v___x_223_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_array_219_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_stop_221_);
v___x_241_ = v_reuseFailAlloc_255_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___y_245_; 
v___x_242_ = lean_nat_sub(v_endExclusive_237_, v_startInclusive_236_);
v___x_243_ = lean_nat_add(v_fst_227_, v___x_242_);
lean_dec(v___x_242_);
if (v___y_215_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_indentation_235_);
v___x_254_ = lean_unsigned_to_nat(0u);
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
else
{
v___y_245_ = v_indentation_235_;
goto v___jp_244_;
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_246_ = lean_string_utf8_extract_fast(v_s_213_, v_startInclusive_236_, v_endExclusive_237_);
lean_dec(v_endExclusive_237_);
lean_dec(v_startInclusive_236_);
lean_inc(v___x_243_);
lean_inc_ref(v___y_214_);
v___x_247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_247_, 0, v_length_234_);
lean_ctor_set(v___x_247_, 1, v___y_245_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_ctor_set(v___x_247_, 3, v___y_214_);
lean_ctor_set(v___x_247_, 4, v_fst_227_);
lean_ctor_set(v___x_247_, 5, v___x_243_);
v___x_248_ = lean_array_push(v_snd_228_, v___x_247_);
v___x_249_ = lean_nat_add(v___x_243_, v___x_238_);
lean_dec(v___x_243_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_248_);
lean_ctor_set(v___x_230_, 0, v___x_249_);
v___x_251_ = v___x_230_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_248_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v_a_216_ = v___x_241_;
v_b_217_ = v___x_251_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___boxed(lean_object* v_s_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v_a_261_, lean_object* v_b_262_, lean_object* v___y_263_){
_start:
{
uint8_t v___y_3180__boxed_264_; lean_object* v_res_265_; 
v___y_3180__boxed_264_ = lean_unbox(v___y_260_);
v_res_265_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_258_, v___y_259_, v___y_3180__boxed_264_, v_a_261_, v_b_262_, v___y_263_);
lean_dec_ref(v_s_258_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(lean_object* v_s_268_, uint8_t v_isToken_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; lean_object* v_pendingLine_272_; lean_object* v_length_273_; lean_object* v_indentation_274_; lean_object* v_line_275_; lean_object* v_tokenRanges_276_; lean_object* v_startPos_277_; lean_object* v_endPos_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_357_; 
v___x_271_ = lean_string_utf8_byte_size(v_s_268_);
v_pendingLine_272_ = lean_ctor_get(v_a_270_, 1);
lean_inc_ref(v_pendingLine_272_);
v_length_273_ = lean_ctor_get(v_pendingLine_272_, 0);
v_indentation_274_ = lean_ctor_get(v_pendingLine_272_, 1);
v_line_275_ = lean_ctor_get(v_pendingLine_272_, 2);
v_tokenRanges_276_ = lean_ctor_get(v_pendingLine_272_, 3);
v_startPos_277_ = lean_ctor_get(v_pendingLine_272_, 4);
v_endPos_278_ = lean_ctor_get(v_pendingLine_272_, 5);
v_isSharedCheck_357_ = !lean_is_exclusive(v_pendingLine_272_);
if (v_isSharedCheck_357_ == 0)
{
v___x_280_ = v_pendingLine_272_;
v_isShared_281_ = v_isSharedCheck_357_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_endPos_278_);
lean_inc(v_startPos_277_);
lean_inc(v_tokenRanges_276_);
lean_inc(v_line_275_);
lean_inc(v_indentation_274_);
lean_inc(v_length_273_);
lean_dec(v_pendingLine_272_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_357_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_lineInfos_284_; lean_object* v___x_285_; lean_object* v___y_287_; lean_object* v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___x_334_; uint8_t v___y_336_; lean_object* v___y_337_; 
v___x_282_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_268_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_s_268_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_ctor_set(v___x_283_, 2, v___x_271_);
v_lineInfos_284_ = l_Lean_Fmt_collectLineInfos(v___x_283_);
v___x_285_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default));
v___x_334_ = l_Lean_Fmt_instInhabitedLineInfo_default(v___x_283_);
if (v_isToken_269_ == 0)
{
uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_349_ = 1;
v___x_350_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0));
v___y_336_ = v___x_349_;
v___y_337_ = v___x_350_;
goto v___jp_335_;
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_nat_add(v_endPos_278_, v___x_271_);
v___x_352_ = 0;
lean_inc(v_endPos_278_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_endPos_278_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_array_push(v___x_355_, v___x_353_);
v___y_336_ = v___x_352_;
v___y_337_ = v___x_356_;
goto v___jp_335_;
}
v___jp_286_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_294_ = lean_string_utf8_extract_fast(v_s_268_, v___y_288_, v___y_292_);
lean_dec(v___y_292_);
lean_dec(v___y_288_);
v___x_295_ = lean_string_append(v_line_275_, v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = l_Array_append___redArg(v_tokenRanges_276_, v___y_287_);
lean_inc(v___y_291_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 5, v___y_291_);
lean_ctor_set(v___x_280_, 3, v___x_296_);
lean_ctor_set(v___x_280_, 2, v___x_295_);
lean_ctor_set(v___x_280_, 1, v___y_293_);
lean_ctor_set(v___x_280_, 0, v___y_290_);
v___x_298_ = v___x_280_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___y_290_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___y_293_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_startPos_277_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v___y_291_);
v___x_298_ = v_reuseFailAlloc_333_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_fst_307_; lean_object* v_snd_308_; lean_object* v_snd_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_331_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
v___x_301_ = lean_array_push(v___x_300_, v___x_298_);
v___x_302_ = lean_nat_add(v___y_291_, v___x_299_);
lean_dec(v___y_291_);
v___x_303_ = lean_array_get_size(v_lineInfos_284_);
v___x_304_ = l_Array_toSubarray___redArg(v_lineInfos_284_, v___x_299_, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_301_);
v___x_306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_268_, v___y_287_, v___y_289_, v___x_304_, v___x_305_, v_a_270_);
lean_dec_ref(v_s_268_);
v_fst_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_fst_307_);
v_snd_308_ = lean_ctor_get(v___x_306_, 1);
lean_inc(v_snd_308_);
lean_dec_ref(v___x_306_);
v_snd_309_ = lean_ctor_get(v_fst_307_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_fst_307_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_fst_307_, 0);
lean_dec(v_unused_332_);
v___x_311_ = v_fst_307_;
v_isShared_312_ = v_isSharedCheck_331_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_snd_309_);
lean_dec(v_fst_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_331_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_finishedLines_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_329_; 
v_finishedLines_313_ = lean_ctor_get(v_snd_308_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_snd_308_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_snd_308_, 1);
lean_dec(v_unused_330_);
v___x_315_ = v_snd_308_;
v_isShared_316_ = v_isSharedCheck_329_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_finishedLines_313_);
lean_dec(v_snd_308_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_329_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_317_ = lean_array_get_size(v_snd_309_);
v___x_318_ = lean_nat_sub(v___x_317_, v___x_299_);
v___x_319_ = lean_array_get(v___x_285_, v_snd_309_, v___x_318_);
lean_dec(v___x_318_);
v___x_320_ = lean_array_pop(v_snd_309_);
v___x_321_ = lean_box(0);
v___x_322_ = l_Array_append___redArg(v_finishedLines_313_, v___x_320_);
lean_dec_ref(v___x_320_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_319_);
lean_ctor_set(v___x_315_, 0, v___x_322_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_319_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_324_);
lean_ctor_set(v___x_311_, 0, v___x_321_);
v___x_326_ = v___x_311_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
v___jp_335_:
{
lean_object* v___x_338_; lean_object* v_range_339_; lean_object* v_length_340_; lean_object* v_indentation_341_; lean_object* v_startInclusive_342_; lean_object* v_endExclusive_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_338_ = lean_array_get(v___x_334_, v_lineInfos_284_, v___x_282_);
lean_dec_ref(v___x_334_);
v_range_339_ = lean_ctor_get(v___x_338_, 2);
lean_inc_ref(v_range_339_);
v_length_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_length_340_);
v_indentation_341_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_indentation_341_);
lean_dec(v___x_338_);
v_startInclusive_342_ = lean_ctor_get(v_range_339_, 0);
lean_inc(v_startInclusive_342_);
v_endExclusive_343_ = lean_ctor_get(v_range_339_, 1);
lean_inc(v_endExclusive_343_);
lean_dec_ref(v_range_339_);
v___x_344_ = lean_nat_sub(v_endExclusive_343_, v_startInclusive_342_);
v___x_345_ = lean_nat_add(v_endPos_278_, v___x_344_);
lean_dec(v___x_344_);
lean_dec(v_endPos_278_);
v___x_346_ = lean_nat_add(v_length_273_, v_length_340_);
lean_dec(v_length_340_);
v___x_347_ = lean_nat_dec_lt(v_indentation_274_, v_length_273_);
lean_dec(v_length_273_);
if (v___x_347_ == 0)
{
if (v_isToken_269_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_nat_add(v_indentation_274_, v_indentation_341_);
lean_dec(v_indentation_341_);
lean_dec(v_indentation_274_);
v___y_287_ = v___y_337_;
v___y_288_ = v_startInclusive_342_;
v___y_289_ = v___y_336_;
v___y_290_ = v___x_346_;
v___y_291_ = v___x_345_;
v___y_292_ = v_endExclusive_343_;
v___y_293_ = v___x_348_;
goto v___jp_286_;
}
else
{
lean_dec(v_indentation_341_);
v___y_287_ = v___y_337_;
v___y_288_ = v_startInclusive_342_;
v___y_289_ = v___y_336_;
v___y_290_ = v___x_346_;
v___y_291_ = v___x_345_;
v___y_292_ = v_endExclusive_343_;
v___y_293_ = v_indentation_274_;
goto v___jp_286_;
}
}
else
{
lean_dec(v_indentation_341_);
v___y_287_ = v___y_337_;
v___y_288_ = v_startInclusive_342_;
v___y_289_ = v___y_336_;
v___y_290_ = v___x_346_;
v___y_291_ = v___x_345_;
v___y_292_ = v_endExclusive_343_;
v___y_293_ = v_indentation_274_;
goto v___jp_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___boxed(lean_object* v_s_358_, lean_object* v_isToken_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_isToken_boxed_361_; lean_object* v_res_362_; 
v_isToken_boxed_361_ = lean_unbox(v_isToken_359_);
v_res_362_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_s_358_, v_isToken_boxed_361_, v_a_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(lean_object* v_s_363_, lean_object* v___y_364_, uint8_t v___y_365_, lean_object* v_inst_366_, lean_object* v_R_367_, lean_object* v_a_368_, lean_object* v_b_369_, lean_object* v_c_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_363_, v___y_364_, v___y_365_, v_a_368_, v_b_369_, v___y_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___boxed(lean_object* v_s_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v_inst_376_, lean_object* v_R_377_, lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_c_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___y_3400__boxed_382_; lean_object* v_res_383_; 
v___y_3400__boxed_382_ = lean_unbox(v___y_375_);
v_res_383_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(v_s_373_, v___y_374_, v___y_3400__boxed_382_, v_inst_376_, v_R_377_, v_a_378_, v_b_379_, v_c_380_, v___y_381_);
lean_dec_ref(v_s_373_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(lean_object* v_stx_387_, lean_object* v_a_388_){
_start:
{
switch(lean_obj_tag(v_stx_387_))
{
case 0:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_388_);
return v___x_390_;
}
case 1:
{
lean_object* v_kind_391_; lean_object* v_args_392_; lean_object* v___y_394_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_kind_391_ = lean_ctor_get(v_stx_387_, 1);
lean_inc(v_kind_391_);
v_args_392_ = lean_ctor_get(v_stx_387_, 2);
lean_inc_ref(v_args_392_);
lean_dec_ref_known(v_stx_387_, 3);
v___x_408_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1));
v___x_409_ = lean_name_eq(v_kind_391_, v___x_408_);
lean_dec(v_kind_391_);
if (v___x_409_ == 0)
{
v___y_394_ = v_a_388_;
goto v___jp_393_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_array_get_size(v_args_392_);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
v___y_394_ = v_a_388_;
goto v___jp_393_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_array_fget(v_args_392_, v___x_410_);
lean_dec_ref(v_args_392_);
v_stx_387_ = v___x_413_;
goto _start;
}
}
v___jp_393_:
{
lean_object* v___x_395_; size_t v_sz_396_; size_t v___x_397_; lean_object* v___x_398_; lean_object* v_snd_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v___x_395_ = lean_box(0);
v_sz_396_ = lean_array_size(v_args_392_);
v___x_397_ = ((size_t)0ULL);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_args_392_, v_sz_396_, v___x_397_, v___x_395_, v___y_394_);
lean_dec_ref(v_args_392_);
v_snd_399_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_407_);
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_snd_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_395_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_snd_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
case 2:
{
lean_object* v_info_415_; lean_object* v_val_416_; lean_object* v___y_418_; lean_object* v___x_439_; 
v_info_415_ = lean_ctor_get(v_stx_387_, 0);
lean_inc(v_info_415_);
v_val_416_ = lean_ctor_get(v_stx_387_, 1);
lean_inc_ref(v_val_416_);
lean_dec_ref_known(v_stx_387_, 2);
v___x_439_ = l_Lean_SourceInfo_getLeading_x3f(v_info_415_);
if (lean_obj_tag(v___x_439_) == 0)
{
v___y_418_ = v_a_388_;
goto v___jp_417_;
}
else
{
lean_object* v_val_440_; lean_object* v_str_441_; lean_object* v_startPos_442_; lean_object* v_stopPos_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v_snd_447_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
v_str_441_ = lean_ctor_get(v_val_440_, 0);
lean_inc_ref(v_str_441_);
v_startPos_442_ = lean_ctor_get(v_val_440_, 1);
lean_inc(v_startPos_442_);
v_stopPos_443_ = lean_ctor_get(v_val_440_, 2);
lean_inc(v_stopPos_443_);
lean_dec(v_val_440_);
v___x_444_ = lean_string_utf8_extract(v_str_441_, v_startPos_442_, v_stopPos_443_);
lean_dec(v_stopPos_443_);
lean_dec(v_startPos_442_);
lean_dec_ref(v_str_441_);
v___x_445_ = 0;
v___x_446_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_444_, v___x_445_, v_a_388_);
v_snd_447_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_446_);
v___y_418_ = v_snd_447_;
goto v___jp_417_;
}
v___jp_417_:
{
uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_437_; 
v___x_419_ = 1;
v___x_420_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_val_416_, v___x_419_, v___y_418_);
v_snd_421_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_420_, 0);
lean_dec(v_unused_438_);
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_415_);
lean_dec(v_info_415_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_snd_421_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_object* v_val_430_; lean_object* v_str_431_; lean_object* v_startPos_432_; lean_object* v_stopPos_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; 
lean_del_object(v___x_423_);
v_val_430_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_425_, 1);
v_str_431_ = lean_ctor_get(v_val_430_, 0);
lean_inc_ref(v_str_431_);
v_startPos_432_ = lean_ctor_get(v_val_430_, 1);
lean_inc(v_startPos_432_);
v_stopPos_433_ = lean_ctor_get(v_val_430_, 2);
lean_inc(v_stopPos_433_);
lean_dec(v_val_430_);
v___x_434_ = lean_string_utf8_extract(v_str_431_, v_startPos_432_, v_stopPos_433_);
lean_dec(v_stopPos_433_);
lean_dec(v_startPos_432_);
lean_dec_ref(v_str_431_);
v___x_435_ = 0;
v___x_436_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_434_, v___x_435_, v_snd_421_);
return v___x_436_;
}
}
}
}
default: 
{
lean_object* v_info_448_; lean_object* v_rawVal_449_; lean_object* v___y_451_; lean_object* v___x_476_; 
v_info_448_ = lean_ctor_get(v_stx_387_, 0);
lean_inc(v_info_448_);
v_rawVal_449_ = lean_ctor_get(v_stx_387_, 1);
lean_inc_ref(v_rawVal_449_);
lean_dec_ref_known(v_stx_387_, 4);
v___x_476_ = l_Lean_SourceInfo_getLeading_x3f(v_info_448_);
if (lean_obj_tag(v___x_476_) == 0)
{
v___y_451_ = v_a_388_;
goto v___jp_450_;
}
else
{
lean_object* v_val_477_; lean_object* v_str_478_; lean_object* v_startPos_479_; lean_object* v_stopPos_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v_snd_484_; 
v_val_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v___x_476_, 1);
v_str_478_ = lean_ctor_get(v_val_477_, 0);
lean_inc_ref(v_str_478_);
v_startPos_479_ = lean_ctor_get(v_val_477_, 1);
lean_inc(v_startPos_479_);
v_stopPos_480_ = lean_ctor_get(v_val_477_, 2);
lean_inc(v_stopPos_480_);
lean_dec(v_val_477_);
v___x_481_ = lean_string_utf8_extract(v_str_478_, v_startPos_479_, v_stopPos_480_);
lean_dec(v_stopPos_480_);
lean_dec(v_startPos_479_);
lean_dec_ref(v_str_478_);
v___x_482_ = 0;
v___x_483_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_481_, v___x_482_, v_a_388_);
v_snd_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_snd_484_);
lean_dec_ref(v___x_483_);
v___y_451_ = v_snd_484_;
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v_str_452_; lean_object* v_startPos_453_; lean_object* v_stopPos_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v_snd_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_474_; 
v_str_452_ = lean_ctor_get(v_rawVal_449_, 0);
lean_inc_ref(v_str_452_);
v_startPos_453_ = lean_ctor_get(v_rawVal_449_, 1);
lean_inc(v_startPos_453_);
v_stopPos_454_ = lean_ctor_get(v_rawVal_449_, 2);
lean_inc(v_stopPos_454_);
lean_dec_ref(v_rawVal_449_);
v___x_455_ = lean_string_utf8_extract(v_str_452_, v_startPos_453_, v_stopPos_454_);
lean_dec(v_stopPos_454_);
lean_dec(v_startPos_453_);
lean_dec_ref(v_str_452_);
v___x_456_ = 1;
v___x_457_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_455_, v___x_456_, v___y_451_);
v_snd_458_ = lean_ctor_get(v___x_457_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_475_);
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_474_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_snd_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_474_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_448_);
lean_dec(v_info_448_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_box(0);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_458_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_object* v_val_467_; lean_object* v_str_468_; lean_object* v_startPos_469_; lean_object* v_stopPos_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; 
lean_del_object(v___x_460_);
v_val_467_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_462_, 1);
v_str_468_ = lean_ctor_get(v_val_467_, 0);
lean_inc_ref(v_str_468_);
v_startPos_469_ = lean_ctor_get(v_val_467_, 1);
lean_inc(v_startPos_469_);
v_stopPos_470_ = lean_ctor_get(v_val_467_, 2);
lean_inc(v_stopPos_470_);
lean_dec(v_val_467_);
v___x_471_ = lean_string_utf8_extract(v_str_468_, v_startPos_469_, v_stopPos_470_);
lean_dec(v_stopPos_470_);
lean_dec(v_startPos_469_);
lean_dec_ref(v_str_468_);
v___x_472_ = 0;
v___x_473_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_471_, v___x_472_, v_snd_458_);
return v___x_473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(lean_object* v_as_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_b_488_, lean_object* v___y_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_b_488_);
lean_ctor_set(v___x_491_, 1, v___y_489_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v_snd_494_; lean_object* v___x_495_; size_t v___x_496_; size_t v___x_497_; 
v_a_492_ = lean_array_uget_borrowed(v_as_485_, v_i_487_);
lean_inc(v_a_492_);
v___x_493_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_a_492_, v___y_489_);
v_snd_494_ = lean_ctor_get(v___x_493_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_493_);
v___x_495_ = lean_box(0);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_487_, v___x_496_);
v_i_487_ = v___x_497_;
v_b_488_ = v___x_495_;
v___y_489_ = v_snd_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0___boxed(lean_object* v_as_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_505_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_as_499_, v_sz_boxed_504_, v_i_boxed_505_, v_b_502_, v___y_503_);
lean_dec_ref(v_as_499_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object* v_stx_509_){
_start:
{
lean_object* v___y_511_; lean_object* v___x_522_; 
v___x_522_ = l_Lean_Syntax_getStartPos_x3f(v_stx_509_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___y_511_ = v___x_523_;
goto v___jp_510_;
}
else
{
lean_object* v_val_524_; 
v_val_524_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___x_522_, 1);
v___y_511_ = v_val_524_;
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_snd_518_; lean_object* v_finishedLines_519_; lean_object* v_pendingLine_520_; lean_object* v___x_521_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = ((lean_object*)(l_Lean_Fmt_collectSyntaxLineInfos___closed__0));
v___x_514_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0));
lean_inc(v___y_511_);
v___x_515_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_515_, 0, v___x_512_);
lean_ctor_set(v___x_515_, 1, v___x_512_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
lean_ctor_set(v___x_515_, 3, v___x_513_);
lean_ctor_set(v___x_515_, 4, v___y_511_);
lean_ctor_set(v___x_515_, 5, v___y_511_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_stx_509_, v___x_516_);
v_snd_518_ = lean_ctor_get(v___x_517_, 1);
lean_inc(v_snd_518_);
lean_dec_ref(v___x_517_);
v_finishedLines_519_ = lean_ctor_get(v_snd_518_, 0);
lean_inc_ref(v_finishedLines_519_);
v_pendingLine_520_ = lean_ctor_get(v_snd_518_, 1);
lean_inc_ref(v_pendingLine_520_);
lean_dec(v_snd_518_);
v___x_521_ = lean_array_push(v_finishedLines_519_, v_pendingLine_520_);
return v___x_521_;
}
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Slice(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* initialize_Lean_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_LineInfo(builtin);
}
#ifdef __cplusplus
}
#endif
