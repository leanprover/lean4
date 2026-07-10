// Lean compiler output
// Module: Lean.Compiler.FFI
// Imports: public import Init.System.FilePath import Init.Data.String.Search
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
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_get_leanc_extra_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0 = (const lean_object*)&l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
static lean_once_cell_t l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
static const lean_string_object l_Lean_Compiler_FFI_getCFlags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lean_Compiler_FFI_getCFlags___closed__0 = (const lean_object*)&l_Lean_Compiler_FFI_getCFlags___closed__0_value;
static const lean_string_object l_Lean_Compiler_FFI_getCFlags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1 = (const lean_object*)&l_Lean_Compiler_FFI_getCFlags___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_FFI_getCFlags___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
lean_object* lean_get_leanc_internal_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ROOT"};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value;
static const lean_string_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6;
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_linker_flags(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_FFI_getLinkerFlags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__0 = (const lean_object*)&l_Lean_Compiler_FFI_getLinkerFlags___closed__0_value;
static const lean_string_object l_Lean_Compiler_FFI_getLinkerFlags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = (const lean_object*)&l_Lean_Compiler_FFI_getLinkerFlags___closed__1_value;
static const lean_string_object l_Lean_Compiler_FFI_getLinkerFlags___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = (const lean_object*)&l_Lean_Compiler_FFI_getLinkerFlags___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
static lean_once_cell_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_get_leanc_extra_flags(v_a_00___x40___internal___hyg_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* v_s_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* v_s_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v_s_8_);
lean_dec_ref(v_s_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object* v_s_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
lean_object* v_it_16_; lean_object* v_startInclusive_17_; lean_object* v_endExclusive_18_; 
if (lean_obj_tag(v_a_13_) == 0)
{
lean_object* v_currPos_28_; lean_object* v_searcher_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_55_; 
v_currPos_28_ = lean_ctor_get(v_a_13_, 0);
v_searcher_29_ = lean_ctor_get(v_a_13_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_55_ == 0)
{
v___x_31_ = v_a_13_;
v_isShared_32_ = v_isSharedCheck_55_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_searcher_29_);
lean_inc(v_currPos_28_);
lean_dec(v_a_13_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_55_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_startInclusive_33_; lean_object* v_endExclusive_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_startInclusive_33_ = lean_ctor_get(v___x_11_, 1);
v_endExclusive_34_ = lean_ctor_get(v___x_11_, 2);
v___x_35_ = lean_nat_sub(v_endExclusive_34_, v_startInclusive_33_);
v___x_36_ = lean_nat_dec_eq(v_searcher_29_, v___x_35_);
lean_dec(v___x_35_);
if (v___x_36_ == 0)
{
uint32_t v___x_37_; uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_37_ = 32;
v___x_38_ = lean_string_utf8_get_fast(v_s_10_, v_searcher_29_);
v___x_39_ = lean_uint32_dec_eq(v___x_38_, v___x_37_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_29_);
lean_dec(v_searcher_29_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v___x_40_);
v___x_42_ = v___x_31_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_currPos_28_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
v_a_13_ = v___x_42_;
goto _start;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_slice_48_; lean_object* v_nextIt_50_; 
v___x_45_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_29_);
v___x_46_ = lean_nat_sub(v___x_45_, v_searcher_29_);
v___x_47_ = lean_nat_add(v_searcher_29_, v___x_46_);
lean_dec(v___x_46_);
v_slice_48_ = l_String_Slice_subslice_x21(v___x_11_, v_currPos_28_, v_searcher_29_);
lean_inc(v___x_47_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v___x_47_);
lean_ctor_set(v___x_31_, 0, v___x_47_);
v_nextIt_50_ = v___x_31_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_47_);
v_nextIt_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v_startInclusive_51_; lean_object* v_endExclusive_52_; 
v_startInclusive_51_ = lean_ctor_get(v_slice_48_, 0);
lean_inc(v_startInclusive_51_);
v_endExclusive_52_ = lean_ctor_get(v_slice_48_, 1);
lean_inc(v_endExclusive_52_);
lean_dec_ref(v_slice_48_);
v_it_16_ = v_nextIt_50_;
v_startInclusive_17_ = v_startInclusive_51_;
v_endExclusive_18_ = v_endExclusive_52_;
goto v___jp_15_;
}
}
}
else
{
lean_object* v___x_54_; 
lean_del_object(v___x_31_);
lean_dec(v_searcher_29_);
v___x_54_ = lean_box(1);
lean_inc(v___x_12_);
v_it_16_ = v___x_54_;
v_startInclusive_17_ = v_currPos_28_;
v_endExclusive_18_ = v___x_12_;
goto v___jp_15_;
}
}
}
else
{
lean_dec(v___x_12_);
lean_dec_ref(v_s_10_);
return v_b_14_;
}
v___jp_15_:
{
lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_19_ = lean_nat_sub(v_endExclusive_18_, v_startInclusive_17_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_bool_not(v___x_21_);
if (v___x_22_ == 0)
{
lean_dec(v_endExclusive_18_);
lean_dec(v_startInclusive_17_);
v_a_13_ = v_it_16_;
goto _start;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_inc_ref(v_s_10_);
v___x_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_24_, 0, v_s_10_);
lean_ctor_set(v___x_24_, 1, v_startInclusive_17_);
lean_ctor_set(v___x_24_, 2, v_endExclusive_18_);
v___x_25_ = l_String_Slice_toString(v___x_24_);
lean_dec_ref_known(v___x_24_, 3);
v___x_26_ = lean_array_push(v_b_14_, v___x_25_);
v_a_13_ = v_it_16_;
v_b_14_ = v___x_26_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* v_s_56_, lean_object* v___x_57_, lean_object* v___x_58_, lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_56_, v___x_57_, v___x_58_, v_a_59_, v_b_60_);
lean_dec_ref(v___x_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_string_utf8_byte_size(v_s_64_);
lean_inc_ref(v_s_64_);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v_s_64_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_66_);
v___x_68_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v___x_67_);
v___x_69_ = ((lean_object*)(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0));
v___x_70_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_64_, v___x_67_, v___x_66_, v___x_68_, v___x_69_);
lean_dec_ref_known(v___x_67_, 3);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* v_s_71_, lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v_inst_74_, lean_object* v_R_75_, lean_object* v_a_76_, lean_object* v_b_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_71_, v___x_72_, v___x_73_, v_a_76_, v_b_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* v_s_79_, lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v_inst_82_, lean_object* v_R_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_79_, v___x_80_, v___x_81_, v_inst_82_, v_R_83_, v_a_84_, v_b_85_);
lean_dec_ref(v___x_80_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_get_leanc_extra_flags(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__0, &l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
v___x_90_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__1, &l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_array_push(v___x_96_, v___x_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* v_leanSysroot_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_99_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
v___x_100_ = l_System_FilePath_join(v_leanSysroot_98_, v___x_99_);
v___x_101_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags___closed__2, &l_Lean_Compiler_FFI_getCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getCFlags___closed__2);
v___x_102_ = lean_array_push(v___x_101_, v___x_100_);
v___x_103_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_104_ = l_Array_append___redArg(v___x_102_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* v_a_00___x40___internal___hyg_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* v_s_108_, lean_object* v_replacement_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v_it_113_; lean_object* v_startPos_114_; lean_object* v_endPos_115_; lean_object* v_it_124_; 
switch(lean_obj_tag(v_a_110_))
{
case 0:
{
lean_object* v_pos_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_142_; 
v_pos_130_ = lean_ctor_get(v_a_110_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_a_110_);
if (v_isSharedCheck_142_ == 0)
{
v___x_132_ = v_a_110_;
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_pos_130_);
lean_dec(v_a_110_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_startInclusive_134_; lean_object* v_endExclusive_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_startInclusive_134_ = lean_ctor_get(v_s_108_, 1);
v_endExclusive_135_ = lean_ctor_get(v_s_108_, 2);
v___x_136_ = lean_nat_sub(v_endExclusive_135_, v_startInclusive_134_);
v___x_137_ = lean_nat_dec_eq(v_pos_130_, v___x_136_);
lean_dec(v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 1);
v___x_139_ = v___x_132_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_pos_130_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
v_it_124_ = v___x_139_;
goto v___jp_123_;
}
}
else
{
lean_object* v___x_141_; 
lean_del_object(v___x_132_);
lean_dec(v_pos_130_);
v___x_141_ = lean_box(3);
v_it_124_ = v___x_141_;
goto v___jp_123_;
}
}
}
case 1:
{
lean_object* v_pos_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_155_; 
v_pos_143_ = lean_ctor_get(v_a_110_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_110_);
if (v_isSharedCheck_155_ == 0)
{
v___x_145_ = v_a_110_;
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_pos_143_);
lean_dec(v_a_110_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_str_147_; lean_object* v_startInclusive_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v_str_147_ = lean_ctor_get(v_s_108_, 0);
v_startInclusive_148_ = lean_ctor_get(v_s_108_, 1);
v___x_149_ = lean_nat_add(v_startInclusive_148_, v_pos_143_);
v___x_150_ = lean_string_utf8_next_fast(v_str_147_, v___x_149_);
lean_dec(v___x_149_);
v___x_151_ = lean_nat_sub(v___x_150_, v_startInclusive_148_);
lean_inc(v___x_151_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 0);
lean_ctor_set(v___x_145_, 0, v___x_151_);
v___x_153_ = v___x_145_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v_it_113_ = v___x_153_;
v_startPos_114_ = v_pos_143_;
v_endPos_115_ = v___x_151_;
goto v___jp_112_;
}
}
}
case 2:
{
lean_object* v_needle_156_; lean_object* v_table_157_; lean_object* v_stackPos_158_; lean_object* v_needlePos_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_218_; 
v_needle_156_ = lean_ctor_get(v_a_110_, 0);
v_table_157_ = lean_ctor_get(v_a_110_, 1);
v_stackPos_158_ = lean_ctor_get(v_a_110_, 2);
v_needlePos_159_ = lean_ctor_get(v_a_110_, 3);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_110_);
if (v_isSharedCheck_218_ == 0)
{
v___x_161_ = v_a_110_;
v_isShared_162_ = v_isSharedCheck_218_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_needlePos_159_);
lean_inc(v_stackPos_158_);
lean_inc(v_table_157_);
lean_inc(v_needle_156_);
lean_dec(v_a_110_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_218_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_str_163_; lean_object* v_startInclusive_164_; lean_object* v_endExclusive_165_; lean_object* v_str_166_; lean_object* v_startInclusive_167_; lean_object* v_endExclusive_168_; lean_object* v_basePos_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_str_163_ = lean_ctor_get(v_needle_156_, 0);
v_startInclusive_164_ = lean_ctor_get(v_needle_156_, 1);
v_endExclusive_165_ = lean_ctor_get(v_needle_156_, 2);
v_str_166_ = lean_ctor_get(v_s_108_, 0);
v_startInclusive_167_ = lean_ctor_get(v_s_108_, 1);
v_endExclusive_168_ = lean_ctor_get(v_s_108_, 2);
v_basePos_169_ = lean_nat_sub(v_stackPos_158_, v_needlePos_159_);
v___x_170_ = lean_nat_sub(v_endExclusive_165_, v_startInclusive_164_);
v___x_171_ = lean_nat_add(v_basePos_169_, v___x_170_);
v___x_172_ = lean_nat_sub(v_endExclusive_168_, v_startInclusive_167_);
v___x_173_ = lean_nat_dec_le(v___x_171_, v___x_172_);
lean_dec(v___x_171_);
if (v___x_173_ == 0)
{
uint8_t v___x_174_; 
lean_dec(v___x_170_);
lean_del_object(v___x_161_);
lean_dec(v_needlePos_159_);
lean_dec(v_stackPos_158_);
lean_dec_ref(v_table_157_);
lean_dec_ref(v_needle_156_);
v___x_174_ = lean_nat_dec_lt(v_basePos_169_, v___x_172_);
if (v___x_174_ == 0)
{
lean_dec(v___x_172_);
lean_dec(v_basePos_169_);
lean_dec_ref(v_s_108_);
return v_b_111_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_String_Slice_pos_x21(v_s_108_, v_basePos_169_);
lean_dec(v_basePos_169_);
v___x_176_ = lean_box(3);
v_it_113_ = v___x_176_;
v_startPos_114_ = v___x_175_;
v_endPos_115_ = v___x_172_;
goto v___jp_112_;
}
}
else
{
lean_object* v___x_177_; uint8_t v_stackByte_178_; lean_object* v___x_179_; uint8_t v_patByte_180_; uint8_t v___x_181_; 
lean_dec(v___x_172_);
v___x_177_ = lean_nat_add(v_startInclusive_167_, v_stackPos_158_);
v_stackByte_178_ = lean_string_get_byte_fast(v_str_166_, v___x_177_);
v___x_179_ = lean_nat_add(v_startInclusive_164_, v_needlePos_159_);
v_patByte_180_ = lean_string_get_byte_fast(v_str_163_, v___x_179_);
v___x_181_ = lean_uint8_dec_eq(v_stackByte_178_, v_patByte_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; uint8_t v___x_183_; 
lean_dec(v___x_170_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_nat_dec_eq(v_needlePos_159_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_newNeedlePos_186_; uint8_t v___x_187_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_sub(v_needlePos_159_, v___x_184_);
lean_dec(v_needlePos_159_);
v_newNeedlePos_186_ = lean_array_fget_borrowed(v_table_157_, v___x_185_);
lean_dec(v___x_185_);
v___x_187_ = lean_nat_dec_eq(v_newNeedlePos_186_, v___x_182_);
if (v___x_187_ == 0)
{
lean_object* v_oldBasePos_188_; lean_object* v___x_189_; lean_object* v_newBasePos_190_; lean_object* v___x_192_; 
lean_inc(v_newNeedlePos_186_);
v_oldBasePos_188_ = l_String_Slice_pos_x21(v_s_108_, v_basePos_169_);
lean_dec(v_basePos_169_);
v___x_189_ = lean_nat_sub(v_stackPos_158_, v_newNeedlePos_186_);
v_newBasePos_190_ = l_String_Slice_pos_x21(v_s_108_, v___x_189_);
lean_dec(v___x_189_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v_newNeedlePos_186_);
v___x_192_ = v___x_161_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_needle_156_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_table_157_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_stackPos_158_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_newNeedlePos_186_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
v_it_113_ = v___x_192_;
v_startPos_114_ = v_oldBasePos_188_;
v_endPos_115_ = v_newBasePos_190_;
goto v___jp_112_;
}
}
else
{
lean_object* v_basePos_194_; lean_object* v_nextStackPos_195_; lean_object* v___x_197_; 
v_basePos_194_ = l_String_Slice_pos_x21(v_s_108_, v_basePos_169_);
lean_dec(v_basePos_169_);
v_nextStackPos_195_ = l_String_Slice_posGE___redArg(v_s_108_, v_stackPos_158_);
lean_inc(v_nextStackPos_195_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v___x_182_);
lean_ctor_set(v___x_161_, 2, v_nextStackPos_195_);
v___x_197_ = v___x_161_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_needle_156_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_table_157_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_nextStackPos_195_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_182_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v_it_113_ = v___x_197_;
v_startPos_114_ = v_basePos_194_;
v_endPos_115_ = v_nextStackPos_195_;
goto v___jp_112_;
}
}
}
else
{
lean_object* v_basePos_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_nextStackPos_202_; lean_object* v___x_204_; 
lean_dec(v_basePos_169_);
lean_dec(v_needlePos_159_);
v_basePos_199_ = l_String_Slice_pos_x21(v_s_108_, v_stackPos_158_);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_stackPos_158_, v___x_200_);
lean_dec(v_stackPos_158_);
v_nextStackPos_202_ = l_String_Slice_posGE___redArg(v_s_108_, v___x_201_);
lean_inc(v_nextStackPos_202_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v___x_182_);
lean_ctor_set(v___x_161_, 2, v_nextStackPos_202_);
v___x_204_ = v___x_161_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_needle_156_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_table_157_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_nextStackPos_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v___x_182_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
v_it_113_ = v___x_204_;
v_startPos_114_ = v_basePos_199_;
v_endPos_115_ = v_nextStackPos_202_;
goto v___jp_112_;
}
}
}
else
{
lean_object* v___x_206_; lean_object* v_nextStackPos_207_; lean_object* v_nextNeedlePos_208_; uint8_t v___x_209_; 
lean_dec(v_basePos_169_);
v___x_206_ = lean_unsigned_to_nat(1u);
v_nextStackPos_207_ = lean_nat_add(v_stackPos_158_, v___x_206_);
lean_dec(v_stackPos_158_);
v_nextNeedlePos_208_ = lean_nat_add(v_needlePos_159_, v___x_206_);
lean_dec(v_needlePos_159_);
v___x_209_ = lean_nat_dec_eq(v_nextNeedlePos_208_, v___x_170_);
lean_dec(v___x_170_);
if (v___x_209_ == 0)
{
lean_object* v___x_211_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v_nextNeedlePos_208_);
lean_ctor_set(v___x_161_, 2, v_nextStackPos_207_);
v___x_211_ = v___x_161_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_needle_156_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_table_157_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_nextStackPos_207_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_nextNeedlePos_208_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v_a_110_ = v___x_211_;
goto _start;
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec(v_nextNeedlePos_208_);
v___x_214_ = lean_unsigned_to_nat(0u);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v___x_214_);
lean_ctor_set(v___x_161_, 2, v_nextStackPos_207_);
v___x_216_ = v___x_161_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_needle_156_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_table_157_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_nextStackPos_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
v_it_124_ = v___x_216_;
goto v___jp_123_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_108_);
return v_b_111_;
}
}
v___jp_112_:
{
lean_object* v___x_116_; lean_object* v_str_117_; lean_object* v_startInclusive_118_; lean_object* v_endExclusive_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc_ref(v_s_108_);
v___x_116_ = l_String_Slice_slice_x21(v_s_108_, v_startPos_114_, v_endPos_115_);
lean_dec(v_endPos_115_);
lean_dec(v_startPos_114_);
v_str_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc_ref(v_str_117_);
v_startInclusive_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_startInclusive_118_);
v_endExclusive_119_ = lean_ctor_get(v___x_116_, 2);
lean_inc(v_endExclusive_119_);
lean_dec_ref(v___x_116_);
v___x_120_ = lean_string_utf8_extract(v_str_117_, v_startInclusive_118_, v_endExclusive_119_);
lean_dec(v_endExclusive_119_);
lean_dec(v_startInclusive_118_);
lean_dec_ref(v_str_117_);
v___x_121_ = lean_string_append(v_b_111_, v___x_120_);
lean_dec_ref(v___x_120_);
v_a_110_ = v_it_113_;
v_b_111_ = v___x_121_;
goto _start;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_string_utf8_byte_size(v_replacement_109_);
v___x_127_ = lean_string_utf8_extract(v_replacement_109_, v___x_125_, v___x_126_);
v___x_128_ = lean_string_append(v_b_111_, v___x_127_);
lean_dec_ref(v___x_127_);
v_a_110_ = v_it_124_;
v_b_111_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* v_s_219_, lean_object* v_replacement_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_219_, v_replacement_220_, v_a_221_, v_b_222_);
lean_dec_ref(v_replacement_220_);
return v_res_223_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_227_ = lean_string_utf8_byte_size(v___x_226_);
return v___x_227_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_230_ = lean_nat_dec_eq(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_236_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
v___x_239_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_240_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_237_);
lean_ctor_set(v___x_240_, 3, v___x_237_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* v_s_243_, lean_object* v_replacement_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
v___x_246_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
v___x_248_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_243_, v_replacement_244_, v___x_247_, v___x_245_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7));
v___x_250_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_243_, v_replacement_244_, v___x_249_, v___x_245_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* v_s_251_, lean_object* v_replacement_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_251_, v_replacement_252_);
lean_dec_ref(v_replacement_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* v_leanSysroot_254_, size_t v_sz_255_, size_t v_i_256_, lean_object* v_bs_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_usize_dec_lt(v_i_256_, v_sz_255_);
if (v___x_258_ == 0)
{
return v_bs_257_;
}
else
{
lean_object* v_v_259_; lean_object* v___x_260_; lean_object* v_bs_x27_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; 
v_v_259_ = lean_array_uget(v_bs_257_, v_i_256_);
v___x_260_ = lean_unsigned_to_nat(0u);
v_bs_x27_261_ = lean_array_uset(v_bs_257_, v_i_256_, v___x_260_);
v___x_262_ = lean_string_utf8_byte_size(v_v_259_);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v_v_259_);
lean_ctor_set(v___x_263_, 1, v___x_260_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
v___x_264_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_263_, v_leanSysroot_254_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_256_, v___x_265_);
v___x_267_ = lean_array_uset(v_bs_x27_261_, v_i_256_, v___x_264_);
v_i_256_ = v___x_266_;
v_bs_257_ = v___x_267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* v_leanSysroot_269_, lean_object* v_sz_270_, lean_object* v_i_271_, lean_object* v_bs_272_){
_start:
{
size_t v_sz_boxed_273_; size_t v_i_boxed_274_; lean_object* v_res_275_; 
v_sz_boxed_273_ = lean_unbox_usize(v_sz_270_);
lean_dec(v_sz_270_);
v_i_boxed_274_ = lean_unbox_usize(v_i_271_);
lean_dec(v_i_271_);
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_269_, v_sz_boxed_273_, v_i_boxed_274_, v_bs_272_);
lean_dec_ref(v_leanSysroot_269_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_get_leanc_internal_flags(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__0, &l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
v___x_279_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_278_);
return v___x_279_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2(void){
_start:
{
lean_object* v___x_280_; size_t v_sz_281_; 
v___x_280_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_281_ = lean_array_size(v___x_280_);
return v_sz_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* v_leanSysroot_282_){
_start:
{
lean_object* v___x_283_; size_t v_sz_284_; size_t v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_284_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__2, &l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_282_, v_sz_284_, v___x_285_, v___x_283_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* v_leanSysroot_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_287_);
lean_dec_ref(v_leanSysroot_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* v_s_289_, lean_object* v_pattern_290_, lean_object* v_replacement_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_289_, v_replacement_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* v_s_293_, lean_object* v_pattern_294_, lean_object* v_replacement_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(v_s_293_, v_pattern_294_, v_replacement_295_);
lean_dec_ref(v_replacement_295_);
lean_dec_ref(v_pattern_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* v_s_297_, lean_object* v_replacement_298_, lean_object* v_inst_299_, lean_object* v_R_300_, lean_object* v_a_301_, lean_object* v_b_302_, lean_object* v_c_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_297_, v_replacement_298_, v_a_301_, v_b_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* v_s_305_, lean_object* v_replacement_306_, lean_object* v_inst_307_, lean_object* v_R_308_, lean_object* v_a_309_, lean_object* v_b_310_, lean_object* v_c_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_305_, v_replacement_306_, v_inst_307_, v_R_308_, v_a_309_, v_b_310_, v_c_311_);
lean_dec_ref(v_replacement_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* v_linkStatic_314_){
_start:
{
uint8_t v_linkStatic_boxed_315_; lean_object* v_res_316_; 
v_linkStatic_boxed_315_ = lean_unbox(v_linkStatic_314_);
v_res_316_ = lean_get_linker_flags(v_linkStatic_boxed_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t v_linkStatic_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_get_linker_flags(v_linkStatic_317_);
v___x_319_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* v_linkStatic_320_){
_start:
{
uint8_t v_linkStatic_boxed_321_; lean_object* v_res_322_; 
v_linkStatic_boxed_321_ = lean_unbox(v_linkStatic_320_);
v_res_322_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_boxed_321_);
return v_res_322_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__0));
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_array_push(v___x_328_, v___x_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* v_leanSysroot_330_, uint8_t v_linkStatic_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_332_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__1));
v___x_333_ = l_System_FilePath_join(v_leanSysroot_330_, v___x_332_);
v___x_334_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__2));
v___x_335_ = l_System_FilePath_join(v___x_333_, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_Compiler_FFI_getLinkerFlags___closed__3, &l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once, _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
v___x_337_ = lean_array_push(v___x_336_, v___x_335_);
v___x_338_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_331_);
v___x_339_ = l_Array_append___redArg(v___x_337_, v___x_338_);
lean_dec_ref(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* v_leanSysroot_340_, lean_object* v_linkStatic_341_){
_start:
{
uint8_t v_linkStatic_boxed_342_; lean_object* v_res_343_; 
v_linkStatic_boxed_342_ = lean_unbox(v_linkStatic_341_);
v_res_343_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_340_, v_linkStatic_boxed_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* v_a_00___x40___internal___hyg_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_345_);
return v_res_346_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_get_internal_linker_flags(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
v___x_350_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_349_);
return v___x_350_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2(void){
_start:
{
lean_object* v___x_351_; size_t v_sz_352_; 
v___x_351_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_352_ = lean_array_size(v___x_351_);
return v_sz_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* v_leanSysroot_353_){
_start:
{
lean_object* v___x_354_; size_t v_sz_355_; size_t v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_355_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
v___x_356_ = ((size_t)0ULL);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_353_, v_sz_355_, v___x_356_, v___x_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* v_leanSysroot_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_358_);
lean_dec_ref(v_leanSysroot_358_);
return v_res_359_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_FFI_getCFlags_x27 = _init_l_Lean_Compiler_FFI_getCFlags_x27();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_FFI(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_FFI(builtin);
}
#ifdef __cplusplus
}
#endif
