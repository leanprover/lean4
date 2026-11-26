// Lean compiler output
// Module: Lean.Fmt.FmtM.LineInfo
// Imports: public import Lean.Fmt.FmtM.Error import Init.While import Init.Data.Slice public import Lean.Syntax
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
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f(lean_object* v_stx_1_){
_start:
{
lean_object* v_info_2_; lean_object* v___x_3_; 
v_info_2_ = l_Lean_Syntax_getHeadInfo(v_stx_1_);
v___x_3_ = l_Lean_SourceInfo_getLeading_x3f(v_info_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
uint8_t v___x_4_; lean_object* v___x_5_; 
v___x_4_ = 0;
v___x_5_ = l_Lean_SourceInfo_getPos_x3f(v_info_2_, v___x_4_);
lean_dec(v_info_2_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
lean_dec(v_info_2_);
v_val_6_ = lean_ctor_get(v___x_3_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v___x_3_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_val_6_);
lean_dec(v___x_3_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v_startPos_10_; lean_object* v___x_12_; 
v_startPos_10_ = lean_ctor_get(v_val_6_, 1);
lean_inc(v_startPos_10_);
lean_dec(v_val_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v_startPos_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_startPos_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f___boxed(lean_object* v_stx_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f(v_stx_15_);
lean_dec(v_stx_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo_default(lean_object* v_s_17_){
_start:
{
lean_object* v_startInclusive_18_; lean_object* v_endExclusive_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
v_startInclusive_18_ = lean_ctor_get(v_s_17_, 1);
v_endExclusive_19_ = lean_ctor_get(v_s_17_, 2);
v_isSharedCheck_29_ = !lean_is_exclusive(v_s_17_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; 
v_unused_30_ = lean_ctor_get(v_s_17_, 0);
lean_dec(v_unused_30_);
v___x_21_ = v_s_17_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_endExclusive_19_);
lean_inc(v_startInclusive_18_);
lean_dec(v_s_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_sub(v_endExclusive_19_, v_startInclusive_18_);
lean_dec(v_startInclusive_18_);
lean_dec(v_endExclusive_19_);
lean_inc(v___x_24_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_25_);
lean_ctor_set(v___x_21_, 1, v___x_23_);
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedLineInfo(lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Fmt_instInhabitedLineInfo_default(v_a_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(lean_object* v___x_33_, lean_object* v_____r_34_, lean_object* v_r_35_, lean_object* v_lineLength_36_, lean_object* v_lineIndentation_37_, uint8_t v_foundNonSpaceChar_38_, lean_object* v_lineStartPos_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v_lineStartPos_39_);
lean_ctor_set(v___x_40_, 1, v___x_33_);
v___x_41_ = lean_box(v_foundNonSpaceChar_38_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v_lineIndentation_37_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v_lineLength_36_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_r_35_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0___boxed(lean_object* v___x_47_, lean_object* v_____r_48_, lean_object* v_r_49_, lean_object* v_lineLength_50_, lean_object* v_lineIndentation_51_, lean_object* v_foundNonSpaceChar_52_, lean_object* v_lineStartPos_53_){
_start:
{
uint8_t v_foundNonSpaceChar_boxed_54_; lean_object* v_res_55_; 
v_foundNonSpaceChar_boxed_54_ = lean_unbox(v_foundNonSpaceChar_52_);
v_res_55_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_47_, v_____r_48_, v_r_49_, v_lineLength_50_, v_lineIndentation_51_, v_foundNonSpaceChar_boxed_54_, v_lineStartPos_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(lean_object* v_s_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___y_59_; lean_object* v_snd_63_; lean_object* v_snd_64_; lean_object* v_snd_65_; lean_object* v_snd_66_; lean_object* v_fst_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_142_; 
v_snd_63_ = lean_ctor_get(v_a_57_, 1);
lean_inc(v_snd_63_);
v_snd_64_ = lean_ctor_get(v_snd_63_, 1);
lean_inc(v_snd_64_);
v_snd_65_ = lean_ctor_get(v_snd_64_, 1);
lean_inc(v_snd_65_);
v_snd_66_ = lean_ctor_get(v_snd_65_, 1);
lean_inc(v_snd_66_);
v_fst_67_ = lean_ctor_get(v_a_57_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_a_57_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_a_57_, 1);
lean_dec(v_unused_143_);
v___x_69_ = v_a_57_;
v_isShared_70_ = v_isSharedCheck_142_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_fst_67_);
lean_dec(v_a_57_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_142_;
goto v_resetjp_68_;
}
v___jp_58_:
{
if (lean_obj_tag(v___y_59_) == 0)
{
lean_object* v_a_60_; 
v_a_60_ = lean_ctor_get(v___y_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref_known(v___y_59_, 1);
return v_a_60_;
}
else
{
lean_object* v_a_61_; 
v_a_61_ = lean_ctor_get(v___y_59_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___y_59_, 1);
v_a_57_ = v_a_61_;
goto _start;
}
}
v_resetjp_68_:
{
lean_object* v_fst_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_140_; 
v_fst_71_ = lean_ctor_get(v_snd_63_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_snd_63_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_snd_63_, 1);
lean_dec(v_unused_141_);
v___x_73_ = v_snd_63_;
v_isShared_74_ = v_isSharedCheck_140_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_fst_71_);
lean_dec(v_snd_63_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_140_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_fst_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_138_; 
v_fst_75_ = lean_ctor_get(v_snd_64_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v_snd_64_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v_snd_64_, 1);
lean_dec(v_unused_139_);
v___x_77_ = v_snd_64_;
v_isShared_78_ = v_isSharedCheck_138_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_fst_75_);
lean_dec(v_snd_64_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_138_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_fst_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_136_; 
v_fst_79_ = lean_ctor_get(v_snd_65_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_snd_65_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_snd_65_, 1);
lean_dec(v_unused_137_);
v___x_81_ = v_snd_65_;
v_isShared_82_ = v_isSharedCheck_136_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_fst_79_);
lean_dec(v_snd_65_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_136_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_135_; 
v_fst_83_ = lean_ctor_get(v_snd_66_, 0);
v_snd_84_ = lean_ctor_get(v_snd_66_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_snd_66_);
if (v_isSharedCheck_135_ == 0)
{
v___x_86_ = v_snd_66_;
v_isShared_87_ = v_isSharedCheck_135_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_snd_84_);
lean_inc(v_fst_83_);
lean_dec(v_snd_66_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_135_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_str_88_; lean_object* v_startInclusive_89_; lean_object* v_endExclusive_90_; lean_object* v___x_91_; uint8_t v_decide_92_; 
v_str_88_ = lean_ctor_get(v_s_56_, 0);
v_startInclusive_89_ = lean_ctor_get(v_s_56_, 1);
v_endExclusive_90_ = lean_ctor_get(v_s_56_, 2);
v___x_91_ = lean_nat_sub(v_endExclusive_90_, v_startInclusive_89_);
v_decide_92_ = lean_nat_dec_eq(v_snd_84_, v___x_91_);
lean_dec(v___x_91_);
if (v_decide_92_ == 0)
{
lean_object* v_lineLength_93_; uint8_t v___x_94_; lean_object* v___x_95_; uint32_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint32_t v___x_111_; uint8_t v___x_112_; 
lean_del_object(v___x_86_);
lean_del_object(v___x_81_);
lean_del_object(v___x_77_);
lean_del_object(v___x_73_);
lean_del_object(v___x_69_);
v_lineLength_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = 1;
v___x_95_ = lean_nat_add(v_startInclusive_89_, v_snd_84_);
v___x_96_ = lean_string_utf8_get_fast(v_str_88_, v___x_95_);
v___x_97_ = lean_string_utf8_next_fast(v_str_88_, v___x_95_);
lean_dec(v___x_95_);
v___x_98_ = lean_nat_sub(v___x_97_, v_startInclusive_89_);
v___x_111_ = 32;
v___x_112_ = lean_uint32_dec_eq(v___x_96_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec(v_fst_79_);
goto v___jp_99_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = lean_unbox(v_fst_79_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
lean_dec(v_snd_84_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_fst_71_, v___x_114_);
lean_dec(v_fst_71_);
v___x_116_ = lean_nat_add(v_fst_75_, v___x_114_);
lean_dec(v_fst_75_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_unbox(v_fst_79_);
lean_dec(v_fst_79_);
v___x_119_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_98_, v___x_117_, v_fst_67_, v___x_115_, v___x_116_, v___x_118_, v_fst_83_);
v___y_59_ = v___x_119_;
goto v___jp_58_;
}
else
{
lean_dec(v_fst_79_);
goto v___jp_99_;
}
}
v___jp_99_:
{
uint32_t v___x_100_; uint8_t v___x_101_; 
v___x_100_ = 10;
v___x_101_ = lean_uint32_dec_eq(v___x_96_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_snd_84_);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_fst_71_, v___x_102_);
lean_dec(v_fst_71_);
v___x_104_ = lean_box(0);
v___x_105_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_98_, v___x_104_, v_fst_67_, v___x_103_, v_fst_75_, v___x_94_, v_fst_83_);
v___y_59_ = v___x_105_;
goto v___jp_58_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = l_String_Slice_subslice_x21(v_s_56_, v_fst_83_, v_snd_84_);
v___x_107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_107_, 0, v_fst_71_);
lean_ctor_set(v___x_107_, 1, v_fst_75_);
lean_ctor_set(v___x_107_, 2, v___x_106_);
v___x_108_ = lean_array_push(v_fst_67_, v___x_107_);
v___x_109_ = lean_box(0);
lean_inc(v___x_98_);
v___x_110_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___lam__0(v___x_98_, v___x_109_, v___x_108_, v_lineLength_93_, v_lineLength_93_, v_decide_92_, v___x_98_);
v___y_59_ = v___x_110_;
goto v___jp_58_;
}
}
}
else
{
lean_object* v___x_121_; 
if (v_isShared_87_ == 0)
{
v___x_121_ = v___x_86_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_fst_83_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_snd_84_);
v___x_121_ = v_reuseFailAlloc_134_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_121_);
v___x_123_ = v___x_81_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_fst_79_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_133_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_123_);
v___x_125_ = v___x_77_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fst_75_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_132_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_125_);
v___x_127_ = v___x_73_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_fst_71_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v___x_127_);
v___x_129_ = v___x_69_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_fst_67_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg___boxed(lean_object* v_s_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_144_, v_a_145_);
lean_dec_ref(v_s_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos(lean_object* v_s_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_snd_167_; lean_object* v_snd_168_; lean_object* v_snd_169_; lean_object* v_snd_170_; lean_object* v_fst_171_; lean_object* v_fst_172_; lean_object* v_fst_173_; lean_object* v_fst_174_; lean_object* v_snd_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_165_ = ((lean_object*)(l_Lean_Fmt_collectLineInfos___closed__5));
v___x_166_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_164_, v___x_165_);
v_snd_167_ = lean_ctor_get(v___x_166_, 1);
lean_inc(v_snd_167_);
v_snd_168_ = lean_ctor_get(v_snd_167_, 1);
lean_inc(v_snd_168_);
v_snd_169_ = lean_ctor_get(v_snd_168_, 1);
v_snd_170_ = lean_ctor_get(v_snd_169_, 1);
lean_inc(v_snd_170_);
v_fst_171_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_fst_171_);
lean_dec_ref(v___x_166_);
v_fst_172_ = lean_ctor_get(v_snd_167_, 0);
lean_inc(v_fst_172_);
lean_dec(v_snd_167_);
v_fst_173_ = lean_ctor_get(v_snd_168_, 0);
lean_inc(v_fst_173_);
lean_dec(v_snd_168_);
v_fst_174_ = lean_ctor_get(v_snd_170_, 0);
lean_inc(v_fst_174_);
v_snd_175_ = lean_ctor_get(v_snd_170_, 1);
lean_inc(v_snd_175_);
lean_dec(v_snd_170_);
v___x_176_ = l_String_Slice_subslice_x21(v_s_164_, v_fst_174_, v_snd_175_);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_fst_172_);
lean_ctor_set(v___x_177_, 1, v_fst_173_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
v___x_178_ = lean_array_push(v_fst_171_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectLineInfos___boxed(lean_object* v_s_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Fmt_collectLineInfos(v_s_179_);
lean_dec_ref(v_s_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0(lean_object* v_s_181_, lean_object* v_inst_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___redArg(v_s_181_, v_a_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0___boxed(lean_object* v_s_185_, lean_object* v_inst_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_collectLineInfos_spec__0(v_s_185_, v_inst_186_, v_a_187_);
lean_dec_ref(v_s_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0(lean_object* v_li_203_){
_start:
{
lean_object* v_length_204_; lean_object* v_indentation_205_; lean_object* v_line_206_; lean_object* v_startPos_207_; lean_object* v_endPos_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_length_204_ = lean_ctor_get(v_li_203_, 0);
lean_inc(v_length_204_);
v_indentation_205_ = lean_ctor_get(v_li_203_, 1);
lean_inc(v_indentation_205_);
v_line_206_ = lean_ctor_get(v_li_203_, 2);
lean_inc_ref(v_line_206_);
v_startPos_207_ = lean_ctor_get(v_li_203_, 4);
lean_inc(v_startPos_207_);
v_endPos_208_ = lean_ctor_get(v_li_203_, 5);
lean_inc(v_endPos_208_);
lean_dec_ref(v_li_203_);
v___x_209_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__0));
v___x_210_ = lean_string_append(v_line_206_, v___x_209_);
v___x_211_ = l_Nat_reprFast(v_startPos_207_);
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__1));
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
v___x_215_ = l_Nat_reprFast(v_endPos_208_);
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__2));
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
v___x_219_ = l_Nat_reprFast(v_length_204_);
v___x_220_ = lean_string_append(v___x_218_, v___x_219_);
lean_dec_ref(v___x_219_);
v___x_221_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__3));
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
v___x_223_ = l_Nat_reprFast(v_indentation_205_);
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
lean_dec_ref(v___x_223_);
v___x_225_ = ((lean_object*)(l_Lean_Fmt_instToStringSyntaxLineInfo___lam__0___closed__4));
v___x_226_ = lean_string_append(v___x_224_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(lean_object* v_s_229_, lean_object* v___y_230_, uint8_t v___y_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_array_235_; lean_object* v_start_236_; lean_object* v_stop_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_273_; 
v_array_235_ = lean_ctor_get(v_a_232_, 0);
v_start_236_ = lean_ctor_get(v_a_232_, 1);
v_stop_237_ = lean_ctor_get(v_a_232_, 2);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_273_ == 0)
{
v___x_239_ = v_a_232_;
v_isShared_240_ = v_isSharedCheck_273_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_stop_237_);
lean_inc(v_start_236_);
lean_inc(v_array_235_);
lean_dec(v_a_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_273_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_lt(v_start_236_, v_stop_237_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_del_object(v___x_239_);
lean_dec(v_stop_237_);
lean_dec(v_start_236_);
lean_dec_ref(v_array_235_);
lean_dec_ref(v___y_230_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_b_233_);
lean_ctor_set(v___x_242_, 1, v___y_234_);
return v___x_242_;
}
else
{
lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_272_; 
v_fst_243_ = lean_ctor_get(v_b_233_, 0);
v_snd_244_ = lean_ctor_get(v_b_233_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_b_233_);
if (v_isSharedCheck_272_ == 0)
{
v___x_246_ = v_b_233_;
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_inc(v_fst_243_);
lean_dec(v_b_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v_range_249_; lean_object* v_length_250_; lean_object* v_indentation_251_; lean_object* v_startInclusive_252_; lean_object* v_endExclusive_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_248_ = lean_array_fget_borrowed(v_array_235_, v_start_236_);
v_range_249_ = lean_ctor_get(v___x_248_, 2);
v_length_250_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_length_250_);
v_indentation_251_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_indentation_251_);
v_startInclusive_252_ = lean_ctor_get(v_range_249_, 0);
lean_inc(v_startInclusive_252_);
v_endExclusive_253_ = lean_ctor_get(v_range_249_, 1);
lean_inc(v_endExclusive_253_);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_start_236_, v___x_254_);
lean_dec(v_start_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_255_);
v___x_257_ = v___x_239_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_array_235_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_stop_237_);
v___x_257_ = v_reuseFailAlloc_271_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___y_261_; 
v___x_258_ = lean_nat_sub(v_endExclusive_253_, v_startInclusive_252_);
v___x_259_ = lean_nat_add(v_fst_243_, v___x_258_);
lean_dec(v___x_258_);
if (v___y_231_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v_indentation_251_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___y_261_ = v___x_270_;
goto v___jp_260_;
}
else
{
v___y_261_ = v_indentation_251_;
goto v___jp_260_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_262_ = lean_string_utf8_extract_fast(v_s_229_, v_startInclusive_252_, v_endExclusive_253_);
lean_dec(v_endExclusive_253_);
lean_dec(v_startInclusive_252_);
lean_inc(v___x_259_);
lean_inc_ref(v___y_230_);
v___x_263_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_263_, 0, v_length_250_);
lean_ctor_set(v___x_263_, 1, v___y_261_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v___y_230_);
lean_ctor_set(v___x_263_, 4, v_fst_243_);
lean_ctor_set(v___x_263_, 5, v___x_259_);
v___x_264_ = lean_array_push(v_snd_244_, v___x_263_);
v___x_265_ = lean_nat_add(v___x_259_, v___x_254_);
lean_dec(v___x_259_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_264_);
lean_ctor_set(v___x_246_, 0, v___x_265_);
v___x_267_ = v___x_246_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_264_);
v___x_267_ = v_reuseFailAlloc_269_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
v_a_232_ = v___x_257_;
v_b_233_ = v___x_267_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg___boxed(lean_object* v_s_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v___y_279_){
_start:
{
uint8_t v___y_3180__boxed_280_; lean_object* v_res_281_; 
v___y_3180__boxed_280_ = lean_unbox(v___y_276_);
v_res_281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_274_, v___y_275_, v___y_3180__boxed_280_, v_a_277_, v_b_278_, v___y_279_);
lean_dec_ref(v_s_274_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(lean_object* v_s_284_, uint8_t v_isToken_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_287_; lean_object* v_pendingLine_288_; lean_object* v_length_289_; lean_object* v_indentation_290_; lean_object* v_line_291_; lean_object* v_tokenRanges_292_; lean_object* v_startPos_293_; lean_object* v_endPos_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_373_; 
v___x_287_ = lean_string_utf8_byte_size(v_s_284_);
v_pendingLine_288_ = lean_ctor_get(v_a_286_, 1);
lean_inc_ref(v_pendingLine_288_);
v_length_289_ = lean_ctor_get(v_pendingLine_288_, 0);
v_indentation_290_ = lean_ctor_get(v_pendingLine_288_, 1);
v_line_291_ = lean_ctor_get(v_pendingLine_288_, 2);
v_tokenRanges_292_ = lean_ctor_get(v_pendingLine_288_, 3);
v_startPos_293_ = lean_ctor_get(v_pendingLine_288_, 4);
v_endPos_294_ = lean_ctor_get(v_pendingLine_288_, 5);
v_isSharedCheck_373_ = !lean_is_exclusive(v_pendingLine_288_);
if (v_isSharedCheck_373_ == 0)
{
v___x_296_ = v_pendingLine_288_;
v_isShared_297_ = v_isSharedCheck_373_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_endPos_294_);
lean_inc(v_startPos_293_);
lean_inc(v_tokenRanges_292_);
lean_inc(v_line_291_);
lean_inc(v_indentation_290_);
lean_inc(v_length_289_);
lean_dec(v_pendingLine_288_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_373_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_lineInfos_300_; lean_object* v___x_301_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___x_350_; uint8_t v___y_352_; lean_object* v___y_353_; 
v___x_298_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_284_);
v___x_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_299_, 0, v_s_284_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
lean_ctor_set(v___x_299_, 2, v___x_287_);
v_lineInfos_300_ = l_Lean_Fmt_collectLineInfos(v___x_299_);
v___x_301_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default));
v___x_350_ = l_Lean_Fmt_instInhabitedLineInfo_default(v___x_299_);
if (v_isToken_285_ == 0)
{
uint8_t v___x_365_; lean_object* v___x_366_; 
v___x_365_ = 1;
v___x_366_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___closed__0));
v___y_352_ = v___x_365_;
v___y_353_ = v___x_366_;
goto v___jp_351_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_367_ = lean_nat_add(v_endPos_294_, v___x_287_);
v___x_368_ = 0;
lean_inc(v_endPos_294_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_endPos_294_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_mk_empty_array_with_capacity(v___x_370_);
v___x_372_ = lean_array_push(v___x_371_, v___x_369_);
v___y_352_ = v___x_368_;
v___y_353_ = v___x_372_;
goto v___jp_351_;
}
v___jp_302_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_310_ = lean_string_utf8_extract_fast(v_s_284_, v___y_303_, v___y_307_);
lean_dec(v___y_307_);
lean_dec(v___y_303_);
v___x_311_ = lean_string_append(v_line_291_, v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Array_append___redArg(v_tokenRanges_292_, v___y_305_);
lean_inc(v___y_304_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 5, v___y_304_);
lean_ctor_set(v___x_296_, 3, v___x_312_);
lean_ctor_set(v___x_296_, 2, v___x_311_);
lean_ctor_set(v___x_296_, 1, v___y_309_);
lean_ctor_set(v___x_296_, 0, v___y_308_);
v___x_314_ = v___x_296_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___y_308_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___y_309_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_startPos_293_);
lean_ctor_set(v_reuseFailAlloc_349_, 5, v___y_304_);
v___x_314_ = v_reuseFailAlloc_349_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v_snd_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_347_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_mk_empty_array_with_capacity(v___x_315_);
v___x_317_ = lean_array_push(v___x_316_, v___x_314_);
v___x_318_ = lean_nat_add(v___y_304_, v___x_315_);
lean_dec(v___y_304_);
v___x_319_ = lean_array_get_size(v_lineInfos_300_);
v___x_320_ = l_Array_toSubarray___redArg(v_lineInfos_300_, v___x_315_, v___x_319_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_318_);
lean_ctor_set(v___x_321_, 1, v___x_317_);
v___x_322_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_284_, v___y_305_, v___y_306_, v___x_320_, v___x_321_, v_a_286_);
lean_dec_ref(v_s_284_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v_snd_325_ = lean_ctor_get(v_fst_323_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_fst_323_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_fst_323_, 0);
lean_dec(v_unused_348_);
v___x_327_ = v_fst_323_;
v_isShared_328_ = v_isSharedCheck_347_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snd_325_);
lean_dec(v_fst_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_347_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_finishedLines_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_345_; 
v_finishedLines_329_ = lean_ctor_get(v_snd_324_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_snd_324_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_snd_324_, 1);
lean_dec(v_unused_346_);
v___x_331_ = v_snd_324_;
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_finishedLines_329_);
lean_dec(v_snd_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_333_ = lean_array_get_size(v_snd_325_);
v___x_334_ = lean_nat_sub(v___x_333_, v___x_315_);
v___x_335_ = lean_array_get(v___x_301_, v_snd_325_, v___x_334_);
lean_dec(v___x_334_);
v___x_336_ = lean_array_pop(v_snd_325_);
v___x_337_ = lean_box(0);
v___x_338_ = l_Array_append___redArg(v_finishedLines_329_, v___x_336_);
lean_dec_ref(v___x_336_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_335_);
lean_ctor_set(v___x_331_, 0, v___x_338_);
v___x_340_ = v___x_331_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_335_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_340_);
lean_ctor_set(v___x_327_, 0, v___x_337_);
v___x_342_ = v___x_327_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
v___jp_351_:
{
lean_object* v___x_354_; lean_object* v_range_355_; lean_object* v_length_356_; lean_object* v_indentation_357_; lean_object* v_startInclusive_358_; lean_object* v_endExclusive_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_354_ = lean_array_get(v___x_350_, v_lineInfos_300_, v___x_298_);
lean_dec_ref(v___x_350_);
v_range_355_ = lean_ctor_get(v___x_354_, 2);
lean_inc_ref(v_range_355_);
v_length_356_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_length_356_);
v_indentation_357_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_indentation_357_);
lean_dec(v___x_354_);
v_startInclusive_358_ = lean_ctor_get(v_range_355_, 0);
lean_inc(v_startInclusive_358_);
v_endExclusive_359_ = lean_ctor_get(v_range_355_, 1);
lean_inc(v_endExclusive_359_);
lean_dec_ref(v_range_355_);
v___x_360_ = lean_nat_sub(v_endExclusive_359_, v_startInclusive_358_);
v___x_361_ = lean_nat_add(v_endPos_294_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v_endPos_294_);
v___x_362_ = lean_nat_add(v_length_289_, v_length_356_);
lean_dec(v_length_356_);
v___x_363_ = lean_nat_dec_lt(v_indentation_290_, v_length_289_);
lean_dec(v_length_289_);
if (v___x_363_ == 0)
{
if (v_isToken_285_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_nat_add(v_indentation_290_, v_indentation_357_);
lean_dec(v_indentation_357_);
lean_dec(v_indentation_290_);
v___y_303_ = v_startInclusive_358_;
v___y_304_ = v___x_361_;
v___y_305_ = v___y_353_;
v___y_306_ = v___y_352_;
v___y_307_ = v_endExclusive_359_;
v___y_308_ = v___x_362_;
v___y_309_ = v___x_364_;
goto v___jp_302_;
}
else
{
lean_dec(v_indentation_357_);
v___y_303_ = v_startInclusive_358_;
v___y_304_ = v___x_361_;
v___y_305_ = v___y_353_;
v___y_306_ = v___y_352_;
v___y_307_ = v_endExclusive_359_;
v___y_308_ = v___x_362_;
v___y_309_ = v_indentation_290_;
goto v___jp_302_;
}
}
else
{
lean_dec(v_indentation_357_);
v___y_303_ = v_startInclusive_358_;
v___y_304_ = v___x_361_;
v___y_305_ = v___y_353_;
v___y_306_ = v___y_352_;
v___y_307_ = v_endExclusive_359_;
v___y_308_ = v___x_362_;
v___y_309_ = v_indentation_290_;
goto v___jp_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy___boxed(lean_object* v_s_374_, lean_object* v_isToken_375_, lean_object* v_a_376_){
_start:
{
uint8_t v_isToken_boxed_377_; lean_object* v_res_378_; 
v_isToken_boxed_377_ = lean_unbox(v_isToken_375_);
v_res_378_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_s_374_, v_isToken_boxed_377_, v_a_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(lean_object* v_s_379_, lean_object* v___y_380_, uint8_t v___y_381_, lean_object* v_inst_382_, lean_object* v_R_383_, lean_object* v_a_384_, lean_object* v_b_385_, lean_object* v_c_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___redArg(v_s_379_, v___y_380_, v___y_381_, v_a_384_, v_b_385_, v___y_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0___boxed(lean_object* v_s_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v_inst_392_, lean_object* v_R_393_, lean_object* v_a_394_, lean_object* v_b_395_, lean_object* v_c_396_, lean_object* v___y_397_){
_start:
{
uint8_t v___y_3400__boxed_398_; lean_object* v_res_399_; 
v___y_3400__boxed_398_ = lean_unbox(v___y_391_);
v_res_399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy_spec__0(v_s_389_, v___y_390_, v___y_3400__boxed_398_, v_inst_392_, v_R_393_, v_a_394_, v_b_395_, v_c_396_, v___y_397_);
lean_dec_ref(v_s_389_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(lean_object* v_stx_403_, lean_object* v_a_404_){
_start:
{
switch(lean_obj_tag(v_stx_403_))
{
case 0:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_404_);
return v___x_406_;
}
case 1:
{
lean_object* v_kind_407_; lean_object* v_args_408_; lean_object* v___y_410_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_kind_407_ = lean_ctor_get(v_stx_403_, 1);
lean_inc(v_kind_407_);
v_args_408_ = lean_ctor_get(v_stx_403_, 2);
lean_inc_ref(v_args_408_);
lean_dec_ref_known(v_stx_403_, 3);
v___x_424_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go___closed__1));
v___x_425_ = lean_name_eq(v_kind_407_, v___x_424_);
lean_dec(v_kind_407_);
if (v___x_425_ == 0)
{
v___y_410_ = v_a_404_;
goto v___jp_409_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_array_get_size(v_args_408_);
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
v___y_410_ = v_a_404_;
goto v___jp_409_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_array_fget(v_args_408_, v___x_426_);
lean_dec_ref(v_args_408_);
v_stx_403_ = v___x_429_;
goto _start;
}
}
v___jp_409_:
{
lean_object* v___x_411_; size_t v_sz_412_; size_t v___x_413_; lean_object* v___x_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v___x_411_ = lean_box(0);
v_sz_412_ = lean_array_size(v_args_408_);
v___x_413_ = ((size_t)0ULL);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_args_408_, v_sz_412_, v___x_413_, v___x_411_, v___y_410_);
lean_dec_ref(v_args_408_);
v_snd_415_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_423_);
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_411_);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_snd_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
case 2:
{
lean_object* v_info_431_; lean_object* v_val_432_; lean_object* v___y_434_; lean_object* v___x_455_; 
v_info_431_ = lean_ctor_get(v_stx_403_, 0);
lean_inc(v_info_431_);
v_val_432_ = lean_ctor_get(v_stx_403_, 1);
lean_inc_ref(v_val_432_);
lean_dec_ref_known(v_stx_403_, 2);
v___x_455_ = l_Lean_SourceInfo_getLeading_x3f(v_info_431_);
if (lean_obj_tag(v___x_455_) == 0)
{
v___y_434_ = v_a_404_;
goto v___jp_433_;
}
else
{
lean_object* v_val_456_; lean_object* v_str_457_; lean_object* v_startPos_458_; lean_object* v_stopPos_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v_snd_463_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v_str_457_ = lean_ctor_get(v_val_456_, 0);
lean_inc_ref(v_str_457_);
v_startPos_458_ = lean_ctor_get(v_val_456_, 1);
lean_inc(v_startPos_458_);
v_stopPos_459_ = lean_ctor_get(v_val_456_, 2);
lean_inc(v_stopPos_459_);
lean_dec(v_val_456_);
v___x_460_ = lean_string_utf8_extract(v_str_457_, v_startPos_458_, v_stopPos_459_);
lean_dec(v_stopPos_459_);
lean_dec(v_startPos_458_);
lean_dec_ref(v_str_457_);
v___x_461_ = 0;
v___x_462_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_460_, v___x_461_, v_a_404_);
v_snd_463_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v___x_462_);
v___y_434_ = v_snd_463_;
goto v___jp_433_;
}
v___jp_433_:
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_453_; 
v___x_435_ = 1;
v___x_436_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v_val_432_, v___x_435_, v___y_434_);
v_snd_437_ = lean_ctor_get(v___x_436_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_436_, 0);
lean_dec(v_unused_454_);
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_431_);
lean_dec(v_info_431_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_snd_437_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v_val_446_; lean_object* v_str_447_; lean_object* v_startPos_448_; lean_object* v_stopPos_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; 
lean_del_object(v___x_439_);
v_val_446_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_441_, 1);
v_str_447_ = lean_ctor_get(v_val_446_, 0);
lean_inc_ref(v_str_447_);
v_startPos_448_ = lean_ctor_get(v_val_446_, 1);
lean_inc(v_startPos_448_);
v_stopPos_449_ = lean_ctor_get(v_val_446_, 2);
lean_inc(v_stopPos_449_);
lean_dec(v_val_446_);
v___x_450_ = lean_string_utf8_extract(v_str_447_, v_startPos_448_, v_stopPos_449_);
lean_dec(v_stopPos_449_);
lean_dec(v_startPos_448_);
lean_dec_ref(v_str_447_);
v___x_451_ = 0;
v___x_452_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_450_, v___x_451_, v_snd_437_);
return v___x_452_;
}
}
}
}
default: 
{
lean_object* v_info_464_; lean_object* v_rawVal_465_; lean_object* v___y_467_; lean_object* v___x_492_; 
v_info_464_ = lean_ctor_get(v_stx_403_, 0);
lean_inc(v_info_464_);
v_rawVal_465_ = lean_ctor_get(v_stx_403_, 1);
lean_inc_ref(v_rawVal_465_);
lean_dec_ref_known(v_stx_403_, 4);
v___x_492_ = l_Lean_SourceInfo_getLeading_x3f(v_info_464_);
if (lean_obj_tag(v___x_492_) == 0)
{
v___y_467_ = v_a_404_;
goto v___jp_466_;
}
else
{
lean_object* v_val_493_; lean_object* v_str_494_; lean_object* v_startPos_495_; lean_object* v_stopPos_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v_snd_500_; 
v_val_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_492_, 1);
v_str_494_ = lean_ctor_get(v_val_493_, 0);
lean_inc_ref(v_str_494_);
v_startPos_495_ = lean_ctor_get(v_val_493_, 1);
lean_inc(v_startPos_495_);
v_stopPos_496_ = lean_ctor_get(v_val_493_, 2);
lean_inc(v_stopPos_496_);
lean_dec(v_val_493_);
v___x_497_ = lean_string_utf8_extract(v_str_494_, v_startPos_495_, v_stopPos_496_);
lean_dec(v_stopPos_496_);
lean_dec(v_startPos_495_);
lean_dec_ref(v_str_494_);
v___x_498_ = 0;
v___x_499_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_497_, v___x_498_, v_a_404_);
v_snd_500_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_snd_500_);
lean_dec_ref(v___x_499_);
v___y_467_ = v_snd_500_;
goto v___jp_466_;
}
v___jp_466_:
{
lean_object* v_str_468_; lean_object* v_startPos_469_; lean_object* v_stopPos_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_490_; 
v_str_468_ = lean_ctor_get(v_rawVal_465_, 0);
lean_inc_ref(v_str_468_);
v_startPos_469_ = lean_ctor_get(v_rawVal_465_, 1);
lean_inc(v_startPos_469_);
v_stopPos_470_ = lean_ctor_get(v_rawVal_465_, 2);
lean_inc(v_stopPos_470_);
lean_dec_ref(v_rawVal_465_);
v___x_471_ = lean_string_utf8_extract(v_str_468_, v_startPos_469_, v_stopPos_470_);
lean_dec(v_stopPos_470_);
lean_dec(v_startPos_469_);
lean_dec_ref(v_str_468_);
v___x_472_ = 1;
v___x_473_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_471_, v___x_472_, v___y_467_);
v_snd_474_ = lean_ctor_get(v___x_473_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_473_, 0);
lean_dec(v_unused_491_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_464_);
lean_dec(v_info_464_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_474_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v_val_483_; lean_object* v_str_484_; lean_object* v_startPos_485_; lean_object* v_stopPos_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
lean_del_object(v___x_476_);
v_val_483_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_478_, 1);
v_str_484_ = lean_ctor_get(v_val_483_, 0);
lean_inc_ref(v_str_484_);
v_startPos_485_ = lean_ctor_get(v_val_483_, 1);
lean_inc(v_startPos_485_);
v_stopPos_486_ = lean_ctor_get(v_val_483_, 2);
lean_inc(v_stopPos_486_);
lean_dec(v_val_483_);
v___x_487_ = lean_string_utf8_extract(v_str_484_, v_startPos_485_, v_stopPos_486_);
lean_dec(v_stopPos_486_);
lean_dec(v_startPos_485_);
lean_dec_ref(v_str_484_);
v___x_488_ = 0;
v___x_489_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_advanceBy(v___x_487_, v___x_488_, v_snd_474_);
return v___x_489_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_b_504_);
lean_ctor_set(v___x_507_, 1, v___y_505_);
return v___x_507_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_509_; lean_object* v_snd_510_; lean_object* v___x_511_; size_t v___x_512_; size_t v___x_513_; 
v_a_508_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
lean_inc(v_a_508_);
v___x_509_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_a_508_, v___y_505_);
v_snd_510_ = lean_ctor_get(v___x_509_, 1);
lean_inc(v_snd_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_box(0);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_503_, v___x_512_);
v_i_503_ = v___x_513_;
v_b_504_ = v___x_511_;
v___y_505_ = v_snd_510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0___boxed(lean_object* v_as_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_b_518_, lean_object* v___y_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_521_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go_spec__0(v_as_515_, v_sz_boxed_520_, v_i_boxed_521_, v_b_518_, v___y_519_);
lean_dec_ref(v_as_515_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object* v_stx_525_){
_start:
{
lean_object* v___y_527_; lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Syntax_getStartPos_x3f(v_stx_525_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___y_527_ = v___x_539_;
goto v___jp_526_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_538_, 1);
v___y_527_ = v_val_540_;
goto v___jp_526_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_snd_534_; lean_object* v_finishedLines_535_; lean_object* v_pendingLine_536_; lean_object* v___x_537_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = ((lean_object*)(l_Lean_Fmt_collectSyntaxLineInfos___closed__0));
v___x_530_ = ((lean_object*)(l_Lean_Fmt_instInhabitedSyntaxLineInfo_default___closed__0));
lean_inc(v___y_527_);
v___x_531_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_528_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
lean_ctor_set(v___x_531_, 3, v___x_529_);
lean_ctor_set(v___x_531_, 4, v___y_527_);
lean_ctor_set(v___x_531_, 5, v___y_527_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l___private_Lean_Fmt_FmtM_LineInfo_0__Lean_Fmt_collectSyntaxLineInfos_go(v_stx_525_, v___x_532_);
v_snd_534_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_snd_534_);
lean_dec_ref(v___x_533_);
v_finishedLines_535_ = lean_ctor_get(v_snd_534_, 0);
lean_inc_ref(v_finishedLines_535_);
v_pendingLine_536_ = lean_ctor_get(v_snd_534_, 1);
lean_inc_ref(v_pendingLine_536_);
lean_dec(v_snd_534_);
v___x_537_ = lean_array_push(v_finishedLines_535_, v_pendingLine_536_);
return v___x_537_;
}
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice(uint8_t builtin);
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
