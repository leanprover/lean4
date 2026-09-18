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
lean_object* l_Char_utf8Size(uint32_t);
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
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0;
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
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0(void){
_start:
{
uint32_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 10;
v___x_214_ = l_Char_utf8Size(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(lean_object* v_s_215_, lean_object* v___y_216_, uint8_t v___y_217_, lean_object* v_a_218_, lean_object* v_b_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_260_; 
v_array_221_ = lean_ctor_get(v_a_218_, 0);
v_start_222_ = lean_ctor_get(v_a_218_, 1);
v_stop_223_ = lean_ctor_get(v_a_218_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_a_218_);
if (v_isSharedCheck_260_ == 0)
{
v___x_225_ = v_a_218_;
v_isShared_226_ = v_isSharedCheck_260_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_stop_223_);
lean_inc(v_start_222_);
lean_inc(v_array_221_);
lean_dec(v_a_218_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_260_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_del_object(v___x_225_);
lean_dec(v_stop_223_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
lean_dec_ref(v___y_216_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_b_219_);
lean_ctor_set(v___x_228_, 1, v___y_220_);
return v___x_228_;
}
else
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_259_; 
v_fst_229_ = lean_ctor_get(v_b_219_, 0);
v_snd_230_ = lean_ctor_get(v_b_219_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_b_219_);
if (v_isSharedCheck_259_ == 0)
{
v___x_232_ = v_b_219_;
v_isShared_233_ = v_isSharedCheck_259_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v_b_219_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_259_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v_range_235_; lean_object* v_length_236_; lean_object* v_indentation_237_; lean_object* v_startInclusive_238_; lean_object* v_endExclusive_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_234_ = lean_array_fget_borrowed(v_array_221_, v_start_222_);
v_range_235_ = lean_ctor_get(v___x_234_, 2);
v_length_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_length_236_);
v_indentation_237_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_indentation_237_);
v_startInclusive_238_ = lean_ctor_get(v_range_235_, 0);
lean_inc(v_startInclusive_238_);
v_endExclusive_239_ = lean_ctor_get(v_range_235_, 1);
lean_inc(v_endExclusive_239_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_start_222_, v___x_240_);
lean_dec(v_start_222_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_241_);
v___x_243_ = v___x_225_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_array_221_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_stop_223_);
v___x_243_ = v_reuseFailAlloc_258_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___y_247_; 
v___x_244_ = lean_nat_sub(v_endExclusive_239_, v_startInclusive_238_);
v___x_245_ = lean_nat_add(v_fst_229_, v___x_244_);
lean_dec(v___x_244_);
if (v___y_217_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_indentation_237_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___y_247_ = v___x_257_;
goto v___jp_246_;
}
else
{
v___y_247_ = v_indentation_237_;
goto v___jp_246_;
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_248_ = lean_string_utf8_extract_fast(v_s_215_, v_startInclusive_238_, v_endExclusive_239_);
lean_dec(v_endExclusive_239_);
lean_dec(v_startInclusive_238_);
lean_inc(v___x_245_);
lean_inc_ref(v___y_216_);
v___x_249_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_249_, 0, v_length_236_);
lean_ctor_set(v___x_249_, 1, v___y_247_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
lean_ctor_set(v___x_249_, 3, v___y_216_);
lean_ctor_set(v___x_249_, 4, v_fst_229_);
lean_ctor_set(v___x_249_, 5, v___x_245_);
v___x_250_ = lean_array_push(v_snd_230_, v___x_249_);
v___x_251_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0);
v___x_252_ = lean_nat_add(v___x_245_, v___x_251_);
lean_dec(v___x_245_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_250_);
lean_ctor_set(v___x_232_, 0, v___x_252_);
v___x_254_ = v___x_232_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_250_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v_a_218_ = v___x_243_;
v_b_219_ = v___x_254_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___boxed(lean_object* v_s_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___y_2786__boxed_267_; lean_object* v_res_268_; 
v___y_2786__boxed_267_ = lean_unbox(v___y_263_);
v_res_268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_261_, v___y_262_, v___y_2786__boxed_267_, v_a_264_, v_b_265_, v___y_266_);
lean_dec_ref(v_s_261_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(lean_object* v_s_271_, uint8_t v_isToken_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; lean_object* v_pendingLine_275_; lean_object* v_length_276_; lean_object* v_indentation_277_; lean_object* v_line_278_; lean_object* v_tokenRanges_279_; lean_object* v_startPos_280_; lean_object* v_endPos_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_361_; 
v___x_274_ = lean_string_utf8_byte_size(v_s_271_);
v_pendingLine_275_ = lean_ctor_get(v_a_273_, 1);
lean_inc_ref(v_pendingLine_275_);
v_length_276_ = lean_ctor_get(v_pendingLine_275_, 0);
v_indentation_277_ = lean_ctor_get(v_pendingLine_275_, 1);
v_line_278_ = lean_ctor_get(v_pendingLine_275_, 2);
v_tokenRanges_279_ = lean_ctor_get(v_pendingLine_275_, 3);
v_startPos_280_ = lean_ctor_get(v_pendingLine_275_, 4);
v_endPos_281_ = lean_ctor_get(v_pendingLine_275_, 5);
v_isSharedCheck_361_ = !lean_is_exclusive(v_pendingLine_275_);
if (v_isSharedCheck_361_ == 0)
{
v___x_283_ = v_pendingLine_275_;
v_isShared_284_ = v_isSharedCheck_361_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_endPos_281_);
lean_inc(v_startPos_280_);
lean_inc(v_tokenRanges_279_);
lean_inc(v_line_278_);
lean_inc(v_indentation_277_);
lean_inc(v_length_276_);
lean_dec(v_pendingLine_275_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_361_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_lineInfos_287_; lean_object* v___x_288_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___x_338_; uint8_t v___y_340_; lean_object* v___y_341_; 
v___x_285_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_271_);
v___x_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_286_, 0, v_s_271_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_ctor_set(v___x_286_, 2, v___x_274_);
v_lineInfos_287_ = l_Lean_Fmt_collectLineInfos(v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default));
v___x_338_ = l_Lean_Fmt_instInhabitedLineInfo_default(v___x_286_);
if (v_isToken_272_ == 0)
{
uint8_t v___x_353_; lean_object* v___x_354_; 
v___x_353_ = 1;
v___x_354_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0));
v___y_340_ = v___x_353_;
v___y_341_ = v___x_354_;
goto v___jp_339_;
}
else
{
lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = lean_nat_add(v_endPos_281_, v___x_274_);
v___x_356_ = 0;
lean_inc(v_endPos_281_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_endPos_281_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_360_ = lean_array_push(v___x_359_, v___x_357_);
v___y_340_ = v___x_356_;
v___y_341_ = v___x_360_;
goto v___jp_339_;
}
v___jp_289_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_297_ = lean_string_utf8_extract_fast(v_s_271_, v___y_292_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v___y_292_);
v___x_298_ = lean_string_append(v_line_278_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_299_ = l_Array_append___redArg(v_tokenRanges_279_, v___y_293_);
lean_inc(v___y_295_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 5, v___y_295_);
lean_ctor_set(v___x_283_, 3, v___x_299_);
lean_ctor_set(v___x_283_, 2, v___x_298_);
lean_ctor_set(v___x_283_, 1, v___y_296_);
lean_ctor_set(v___x_283_, 0, v___y_291_);
v___x_301_ = v___x_283_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___y_291_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___y_296_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_startPos_280_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v___y_295_);
v___x_301_ = v_reuseFailAlloc_337_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; lean_object* v_snd_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_335_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_mk_empty_array_with_capacity(v___x_302_);
v___x_304_ = lean_array_push(v___x_303_, v___x_301_);
v___x_305_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___closed__0);
v___x_306_ = lean_nat_add(v___y_295_, v___x_305_);
lean_dec(v___y_295_);
v___x_307_ = lean_array_get_size(v_lineInfos_287_);
v___x_308_ = l_Array_toSubarray___redArg(v_lineInfos_287_, v___x_302_, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v___x_304_);
v___x_310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_271_, v___y_293_, v___y_294_, v___x_308_, v___x_309_, v_a_273_);
lean_dec_ref(v_s_271_);
v_fst_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_fst_311_);
v_snd_312_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_snd_312_);
lean_dec_ref(v___x_310_);
v_snd_313_ = lean_ctor_get(v_fst_311_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_fst_311_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_fst_311_, 0);
lean_dec(v_unused_336_);
v___x_315_ = v_fst_311_;
v_isShared_316_ = v_isSharedCheck_335_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_313_);
lean_dec(v_fst_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_335_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_finishedLines_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_333_; 
v_finishedLines_317_ = lean_ctor_get(v_snd_312_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_snd_312_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_snd_312_, 1);
lean_dec(v_unused_334_);
v___x_319_ = v_snd_312_;
v_isShared_320_ = v_isSharedCheck_333_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_finishedLines_317_);
lean_dec(v_snd_312_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_333_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_321_ = lean_array_get_size(v_snd_313_);
v___x_322_ = lean_nat_sub(v___x_321_, v___x_302_);
v___x_323_ = lean_array_get(v___x_288_, v_snd_313_, v___x_322_);
lean_dec(v___x_322_);
v___x_324_ = lean_array_pop(v_snd_313_);
v___x_325_ = lean_box(0);
v___x_326_ = l_Array_append___redArg(v_finishedLines_317_, v___x_324_);
lean_dec_ref(v___x_324_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_323_);
lean_ctor_set(v___x_319_, 0, v___x_326_);
v___x_328_ = v___x_319_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_323_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_328_);
lean_ctor_set(v___x_315_, 0, v___x_325_);
v___x_330_ = v___x_315_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
v___jp_339_:
{
lean_object* v___x_342_; lean_object* v_range_343_; lean_object* v_length_344_; lean_object* v_indentation_345_; lean_object* v_startInclusive_346_; lean_object* v_endExclusive_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_342_ = lean_array_get(v___x_338_, v_lineInfos_287_, v___x_285_);
lean_dec_ref(v___x_338_);
v_range_343_ = lean_ctor_get(v___x_342_, 2);
lean_inc_ref(v_range_343_);
v_length_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_length_344_);
v_indentation_345_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_indentation_345_);
lean_dec(v___x_342_);
v_startInclusive_346_ = lean_ctor_get(v_range_343_, 0);
lean_inc(v_startInclusive_346_);
v_endExclusive_347_ = lean_ctor_get(v_range_343_, 1);
lean_inc(v_endExclusive_347_);
lean_dec_ref(v_range_343_);
v___x_348_ = lean_nat_sub(v_endExclusive_347_, v_startInclusive_346_);
v___x_349_ = lean_nat_add(v_endPos_281_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v_endPos_281_);
v___x_350_ = lean_nat_add(v_length_276_, v_length_344_);
lean_dec(v_length_344_);
v___x_351_ = lean_nat_dec_lt(v_indentation_277_, v_length_276_);
lean_dec(v_length_276_);
if (v___x_351_ == 0)
{
if (v_isToken_272_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_nat_add(v_indentation_277_, v_indentation_345_);
lean_dec(v_indentation_345_);
lean_dec(v_indentation_277_);
v___y_290_ = v_endExclusive_347_;
v___y_291_ = v___x_350_;
v___y_292_ = v_startInclusive_346_;
v___y_293_ = v___y_341_;
v___y_294_ = v___y_340_;
v___y_295_ = v___x_349_;
v___y_296_ = v___x_352_;
goto v___jp_289_;
}
else
{
lean_dec(v_indentation_345_);
v___y_290_ = v_endExclusive_347_;
v___y_291_ = v___x_350_;
v___y_292_ = v_startInclusive_346_;
v___y_293_ = v___y_341_;
v___y_294_ = v___y_340_;
v___y_295_ = v___x_349_;
v___y_296_ = v_indentation_277_;
goto v___jp_289_;
}
}
else
{
lean_dec(v_indentation_345_);
v___y_290_ = v_endExclusive_347_;
v___y_291_ = v___x_350_;
v___y_292_ = v_startInclusive_346_;
v___y_293_ = v___y_341_;
v___y_294_ = v___y_340_;
v___y_295_ = v___x_349_;
v___y_296_ = v_indentation_277_;
goto v___jp_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___boxed(lean_object* v_s_362_, lean_object* v_isToken_363_, lean_object* v_a_364_){
_start:
{
uint8_t v_isToken_boxed_365_; lean_object* v_res_366_; 
v_isToken_boxed_365_ = lean_unbox(v_isToken_363_);
v_res_366_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_s_362_, v_isToken_boxed_365_, v_a_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(lean_object* v_s_367_, lean_object* v___y_368_, uint8_t v___y_369_, lean_object* v_inst_370_, lean_object* v_R_371_, lean_object* v_a_372_, lean_object* v_b_373_, lean_object* v_c_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_367_, v___y_368_, v___y_369_, v_a_372_, v_b_373_, v___y_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___boxed(lean_object* v_s_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v_inst_380_, lean_object* v_R_381_, lean_object* v_a_382_, lean_object* v_b_383_, lean_object* v_c_384_, lean_object* v___y_385_){
_start:
{
uint8_t v___y_3014__boxed_386_; lean_object* v_res_387_; 
v___y_3014__boxed_386_ = lean_unbox(v___y_379_);
v_res_387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(v_s_377_, v___y_378_, v___y_3014__boxed_386_, v_inst_380_, v_R_381_, v_a_382_, v_b_383_, v_c_384_, v___y_385_);
lean_dec_ref(v_s_377_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(lean_object* v_stx_391_, lean_object* v_a_392_){
_start:
{
switch(lean_obj_tag(v_stx_391_))
{
case 0:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_a_392_);
return v___x_394_;
}
case 1:
{
lean_object* v_kind_395_; lean_object* v_args_396_; lean_object* v___y_398_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_kind_395_ = lean_ctor_get(v_stx_391_, 1);
lean_inc(v_kind_395_);
v_args_396_ = lean_ctor_get(v_stx_391_, 2);
lean_inc_ref(v_args_396_);
lean_dec_ref_known(v_stx_391_, 3);
v___x_412_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1));
v___x_413_ = lean_name_eq(v_kind_395_, v___x_412_);
lean_dec(v_kind_395_);
if (v___x_413_ == 0)
{
v___y_398_ = v_a_392_;
goto v___jp_397_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_args_396_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v___y_398_ = v_a_392_;
goto v___jp_397_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_array_fget(v_args_396_, v___x_414_);
lean_dec_ref(v_args_396_);
v_stx_391_ = v___x_417_;
goto _start;
}
}
v___jp_397_:
{
lean_object* v___x_399_; size_t v_sz_400_; size_t v___x_401_; lean_object* v___x_402_; lean_object* v_snd_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v___x_399_ = lean_box(0);
v_sz_400_ = lean_array_size(v_args_396_);
v___x_401_ = ((size_t)0ULL);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_args_396_, v_sz_400_, v___x_401_, v___x_399_, v___y_398_);
lean_dec_ref(v_args_396_);
v_snd_403_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_411_);
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snd_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_399_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_snd_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
case 2:
{
lean_object* v_info_419_; lean_object* v_val_420_; lean_object* v___y_422_; lean_object* v___x_443_; 
v_info_419_ = lean_ctor_get(v_stx_391_, 0);
lean_inc(v_info_419_);
v_val_420_ = lean_ctor_get(v_stx_391_, 1);
lean_inc_ref(v_val_420_);
lean_dec_ref_known(v_stx_391_, 2);
v___x_443_ = l_Lean_SourceInfo_getLeading_x3f(v_info_419_);
if (lean_obj_tag(v___x_443_) == 0)
{
v___y_422_ = v_a_392_;
goto v___jp_421_;
}
else
{
lean_object* v_val_444_; lean_object* v_str_445_; lean_object* v_startPos_446_; lean_object* v_stopPos_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v_snd_451_; 
v_val_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v___x_443_, 1);
v_str_445_ = lean_ctor_get(v_val_444_, 0);
lean_inc_ref(v_str_445_);
v_startPos_446_ = lean_ctor_get(v_val_444_, 1);
lean_inc(v_startPos_446_);
v_stopPos_447_ = lean_ctor_get(v_val_444_, 2);
lean_inc(v_stopPos_447_);
lean_dec(v_val_444_);
v___x_448_ = lean_string_utf8_extract(v_str_445_, v_startPos_446_, v_stopPos_447_);
lean_dec(v_stopPos_447_);
lean_dec(v_startPos_446_);
lean_dec_ref(v_str_445_);
v___x_449_ = 0;
v___x_450_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_448_, v___x_449_, v_a_392_);
v_snd_451_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_snd_451_);
lean_dec_ref(v___x_450_);
v___y_422_ = v_snd_451_;
goto v___jp_421_;
}
v___jp_421_:
{
uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_441_; 
v___x_423_ = 1;
v___x_424_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_val_420_, v___x_423_, v___y_422_);
v_snd_425_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_442_);
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_441_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_441_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_419_);
lean_dec(v_info_419_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_snd_425_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v_val_434_; lean_object* v_str_435_; lean_object* v_startPos_436_; lean_object* v_stopPos_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
lean_del_object(v___x_427_);
v_val_434_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_429_, 1);
v_str_435_ = lean_ctor_get(v_val_434_, 0);
lean_inc_ref(v_str_435_);
v_startPos_436_ = lean_ctor_get(v_val_434_, 1);
lean_inc(v_startPos_436_);
v_stopPos_437_ = lean_ctor_get(v_val_434_, 2);
lean_inc(v_stopPos_437_);
lean_dec(v_val_434_);
v___x_438_ = lean_string_utf8_extract(v_str_435_, v_startPos_436_, v_stopPos_437_);
lean_dec(v_stopPos_437_);
lean_dec(v_startPos_436_);
lean_dec_ref(v_str_435_);
v___x_439_ = 0;
v___x_440_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_438_, v___x_439_, v_snd_425_);
return v___x_440_;
}
}
}
}
default: 
{
lean_object* v_info_452_; lean_object* v_rawVal_453_; lean_object* v___y_455_; lean_object* v___x_480_; 
v_info_452_ = lean_ctor_get(v_stx_391_, 0);
lean_inc(v_info_452_);
v_rawVal_453_ = lean_ctor_get(v_stx_391_, 1);
lean_inc_ref(v_rawVal_453_);
lean_dec_ref_known(v_stx_391_, 4);
v___x_480_ = l_Lean_SourceInfo_getLeading_x3f(v_info_452_);
if (lean_obj_tag(v___x_480_) == 0)
{
v___y_455_ = v_a_392_;
goto v___jp_454_;
}
else
{
lean_object* v_val_481_; lean_object* v_str_482_; lean_object* v_startPos_483_; lean_object* v_stopPos_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v_snd_488_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_480_, 1);
v_str_482_ = lean_ctor_get(v_val_481_, 0);
lean_inc_ref(v_str_482_);
v_startPos_483_ = lean_ctor_get(v_val_481_, 1);
lean_inc(v_startPos_483_);
v_stopPos_484_ = lean_ctor_get(v_val_481_, 2);
lean_inc(v_stopPos_484_);
lean_dec(v_val_481_);
v___x_485_ = lean_string_utf8_extract(v_str_482_, v_startPos_483_, v_stopPos_484_);
lean_dec(v_stopPos_484_);
lean_dec(v_startPos_483_);
lean_dec_ref(v_str_482_);
v___x_486_ = 0;
v___x_487_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_485_, v___x_486_, v_a_392_);
v_snd_488_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_snd_488_);
lean_dec_ref(v___x_487_);
v___y_455_ = v_snd_488_;
goto v___jp_454_;
}
v___jp_454_:
{
lean_object* v_str_456_; lean_object* v_startPos_457_; lean_object* v_stopPos_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_478_; 
v_str_456_ = lean_ctor_get(v_rawVal_453_, 0);
lean_inc_ref(v_str_456_);
v_startPos_457_ = lean_ctor_get(v_rawVal_453_, 1);
lean_inc(v_startPos_457_);
v_stopPos_458_ = lean_ctor_get(v_rawVal_453_, 2);
lean_inc(v_stopPos_458_);
lean_dec_ref(v_rawVal_453_);
v___x_459_ = lean_string_utf8_extract(v_str_456_, v_startPos_457_, v_stopPos_458_);
lean_dec(v_stopPos_458_);
lean_dec(v_startPos_457_);
lean_dec_ref(v_str_456_);
v___x_460_ = 1;
v___x_461_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_459_, v___x_460_, v___y_455_);
v_snd_462_ = lean_ctor_get(v___x_461_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_479_);
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_478_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_478_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_452_);
lean_dec(v_info_452_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_box(0);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_snd_462_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v_val_471_; lean_object* v_str_472_; lean_object* v_startPos_473_; lean_object* v_stopPos_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; 
lean_del_object(v___x_464_);
v_val_471_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_466_, 1);
v_str_472_ = lean_ctor_get(v_val_471_, 0);
lean_inc_ref(v_str_472_);
v_startPos_473_ = lean_ctor_get(v_val_471_, 1);
lean_inc(v_startPos_473_);
v_stopPos_474_ = lean_ctor_get(v_val_471_, 2);
lean_inc(v_stopPos_474_);
lean_dec(v_val_471_);
v___x_475_ = lean_string_utf8_extract(v_str_472_, v_startPos_473_, v_stopPos_474_);
lean_dec(v_stopPos_474_);
lean_dec(v_startPos_473_);
lean_dec_ref(v_str_472_);
v___x_476_ = 0;
v___x_477_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_475_, v___x_476_, v_snd_462_);
return v___x_477_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(lean_object* v_as_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_b_492_);
lean_ctor_set(v___x_495_, 1, v___y_493_);
return v___x_495_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v_snd_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; 
v_a_496_ = lean_array_uget_borrowed(v_as_489_, v_i_491_);
lean_inc(v_a_496_);
v___x_497_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_a_496_, v___y_493_);
v_snd_498_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_snd_498_);
lean_dec_ref(v___x_497_);
v___x_499_ = lean_box(0);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_491_, v___x_500_);
v_i_491_ = v___x_501_;
v_b_492_ = v___x_499_;
v___y_493_ = v_snd_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0___boxed(lean_object* v_as_503_, lean_object* v_sz_504_, lean_object* v_i_505_, lean_object* v_b_506_, lean_object* v___y_507_){
_start:
{
size_t v_sz_boxed_508_; size_t v_i_boxed_509_; lean_object* v_res_510_; 
v_sz_boxed_508_ = lean_unbox_usize(v_sz_504_);
lean_dec(v_sz_504_);
v_i_boxed_509_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_as_503_, v_sz_boxed_508_, v_i_boxed_509_, v_b_506_, v___y_507_);
lean_dec_ref(v_as_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object* v_stx_513_){
_start:
{
lean_object* v___y_515_; lean_object* v___x_526_; 
v___x_526_ = l_Lean_Syntax_getStartPos_x3f(v_stx_513_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___y_515_ = v___x_527_;
goto v___jp_514_;
}
else
{
lean_object* v_val_528_; 
v_val_528_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v___x_526_, 1);
v___y_515_ = v_val_528_;
goto v___jp_514_;
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_snd_522_; lean_object* v_finishedLines_523_; lean_object* v_pendingLine_524_; lean_object* v___x_525_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = ((lean_object*)(l_Lean_Fmt_collectSyntaxLineInfos___closed__0));
v___x_518_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0));
lean_inc(v___y_515_);
v___x_519_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_519_, 0, v___x_516_);
lean_ctor_set(v___x_519_, 1, v___x_516_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
lean_ctor_set(v___x_519_, 3, v___x_517_);
lean_ctor_set(v___x_519_, 4, v___y_515_);
lean_ctor_set(v___x_519_, 5, v___y_515_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_stx_513_, v___x_520_);
v_snd_522_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_snd_522_);
lean_dec_ref(v___x_521_);
v_finishedLines_523_ = lean_ctor_get(v_snd_522_, 0);
lean_inc_ref(v_finishedLines_523_);
v_pendingLine_524_ = lean_ctor_get(v_snd_522_, 1);
lean_inc_ref(v_pendingLine_524_);
lean_dec(v_snd_522_);
v___x_525_ = lean_array_push(v_finishedLines_523_, v_pendingLine_524_);
return v___x_525_;
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
