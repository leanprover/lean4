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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* v_currPos_27_; lean_object* v_searcher_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_51_; 
v_currPos_27_ = lean_ctor_get(v_a_13_, 0);
v_searcher_28_ = lean_ctor_get(v_a_13_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_51_ == 0)
{
v___x_30_ = v_a_13_;
v_isShared_31_ = v_isSharedCheck_51_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_searcher_28_);
lean_inc(v_currPos_27_);
lean_dec(v_a_13_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_51_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v_decide_32_; 
v_decide_32_ = lean_nat_dec_eq(v_searcher_28_, v___x_12_);
if (v_decide_32_ == 0)
{
uint32_t v___x_33_; uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_33_ = 32;
v___x_34_ = lean_string_utf8_get_fast(v_s_10_, v_searcher_28_);
v___x_35_ = lean_uint32_dec_eq(v___x_34_, v___x_33_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_28_);
lean_dec(v_searcher_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_36_);
v___x_38_ = v___x_30_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_currPos_27_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___x_36_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
v_a_13_ = v___x_38_;
goto _start;
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_slice_44_; lean_object* v_nextIt_46_; 
v___x_41_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_28_);
v___x_42_ = lean_nat_sub(v___x_41_, v_searcher_28_);
v___x_43_ = lean_nat_add(v_searcher_28_, v___x_42_);
lean_dec(v___x_42_);
v_slice_44_ = l_String_Slice_subslice_x21(v___x_11_, v_currPos_27_, v_searcher_28_);
lean_inc(v___x_43_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_43_);
lean_ctor_set(v___x_30_, 0, v___x_43_);
v_nextIt_46_ = v___x_30_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_43_);
v_nextIt_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v_startInclusive_47_; lean_object* v_endExclusive_48_; 
v_startInclusive_47_ = lean_ctor_get(v_slice_44_, 0);
lean_inc(v_startInclusive_47_);
v_endExclusive_48_ = lean_ctor_get(v_slice_44_, 1);
lean_inc(v_endExclusive_48_);
lean_dec_ref(v_slice_44_);
v_it_16_ = v_nextIt_46_;
v_startInclusive_17_ = v_startInclusive_47_;
v_endExclusive_18_ = v_endExclusive_48_;
goto v___jp_15_;
}
}
}
else
{
lean_object* v___x_50_; 
lean_del_object(v___x_30_);
lean_dec(v_searcher_28_);
v___x_50_ = lean_box(1);
lean_inc(v___x_12_);
v_it_16_ = v___x_50_;
v_startInclusive_17_ = v_currPos_27_;
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
lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_19_ = lean_nat_sub(v_endExclusive_18_, v_startInclusive_17_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref(v_s_10_);
v___x_22_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_22_, 0, v_s_10_);
lean_ctor_set(v___x_22_, 1, v_startInclusive_17_);
lean_ctor_set(v___x_22_, 2, v_endExclusive_18_);
v___x_23_ = l_String_Slice_toString(v___x_22_);
lean_dec_ref_known(v___x_22_, 3);
v___x_24_ = lean_array_push(v_b_14_, v___x_23_);
v_a_13_ = v_it_16_;
v_b_14_ = v___x_24_;
goto _start;
}
else
{
lean_dec(v_endExclusive_18_);
lean_dec(v_startInclusive_17_);
v_a_13_ = v_it_16_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* v_s_52_, lean_object* v___x_53_, lean_object* v___x_54_, lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_52_, v___x_53_, v___x_54_, v_a_55_, v_b_56_);
lean_dec_ref(v___x_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* v_s_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_string_utf8_byte_size(v_s_60_);
lean_inc_ref(v_s_60_);
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v_s_60_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_62_);
v___x_64_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v___x_63_);
v___x_65_ = ((lean_object*)(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0));
v___x_66_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_60_, v___x_63_, v___x_62_, v___x_64_, v___x_65_);
lean_dec_ref_known(v___x_63_, 3);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* v_s_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v_inst_70_, lean_object* v_R_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_67_, v___x_68_, v___x_69_, v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* v_s_75_, lean_object* v___x_76_, lean_object* v___x_77_, lean_object* v_inst_78_, lean_object* v_R_79_, lean_object* v_a_80_, lean_object* v_b_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_75_, v___x_76_, v___x_77_, v_inst_78_, v_R_79_, v_a_80_, v_b_81_);
lean_dec_ref(v___x_76_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_get_leanc_extra_flags(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__0, &l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
v___x_86_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__1, &l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
v___x_91_ = lean_unsigned_to_nat(2u);
v___x_92_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_93_ = lean_array_push(v___x_92_, v___x_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* v_leanSysroot_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_95_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
v___x_96_ = l_System_FilePath_join(v_leanSysroot_94_, v___x_95_);
v___x_97_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags___closed__2, &l_Lean_Compiler_FFI_getCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getCFlags___closed__2);
v___x_98_ = lean_array_push(v___x_97_, v___x_96_);
v___x_99_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_100_ = l_Array_append___redArg(v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* v_a_00___x40___internal___hyg_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* v_s_104_, lean_object* v_replacement_105_, lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v_it_109_; lean_object* v_startPos_110_; lean_object* v_endPos_111_; lean_object* v_it_120_; 
switch(lean_obj_tag(v_a_106_))
{
case 0:
{
lean_object* v_pos_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_138_; 
v_pos_126_ = lean_ctor_get(v_a_106_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_138_ == 0)
{
v___x_128_ = v_a_106_;
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_pos_126_);
lean_dec(v_a_106_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_startInclusive_130_; lean_object* v_endExclusive_131_; lean_object* v___x_132_; uint8_t v_decide_133_; 
v_startInclusive_130_ = lean_ctor_get(v_s_104_, 1);
v_endExclusive_131_ = lean_ctor_get(v_s_104_, 2);
v___x_132_ = lean_nat_sub(v_endExclusive_131_, v_startInclusive_130_);
v_decide_133_ = lean_nat_dec_eq(v_pos_126_, v___x_132_);
lean_dec(v___x_132_);
if (v_decide_133_ == 0)
{
lean_object* v___x_135_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 1);
v___x_135_ = v___x_128_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_pos_126_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
v_it_120_ = v___x_135_;
goto v___jp_119_;
}
}
else
{
lean_object* v___x_137_; 
lean_del_object(v___x_128_);
lean_dec(v_pos_126_);
v___x_137_ = lean_box(3);
v_it_120_ = v___x_137_;
goto v___jp_119_;
}
}
}
case 1:
{
lean_object* v_pos_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_pos_139_ = lean_ctor_get(v_a_106_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v_a_106_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_pos_139_);
lean_dec(v_a_106_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_str_143_; lean_object* v_startInclusive_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v_str_143_ = lean_ctor_get(v_s_104_, 0);
v_startInclusive_144_ = lean_ctor_get(v_s_104_, 1);
v___x_145_ = lean_nat_add(v_startInclusive_144_, v_pos_139_);
v___x_146_ = lean_string_utf8_next_fast(v_str_143_, v___x_145_);
lean_dec(v___x_145_);
v___x_147_ = lean_nat_sub(v___x_146_, v_startInclusive_144_);
lean_inc(v___x_147_);
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 0);
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v_it_109_ = v___x_149_;
v_startPos_110_ = v_pos_139_;
v_endPos_111_ = v___x_147_;
goto v___jp_108_;
}
}
}
case 2:
{
lean_object* v_needle_152_; lean_object* v_table_153_; lean_object* v_stackPos_154_; lean_object* v_needlePos_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_216_; 
v_needle_152_ = lean_ctor_get(v_a_106_, 0);
v_table_153_ = lean_ctor_get(v_a_106_, 1);
v_stackPos_154_ = lean_ctor_get(v_a_106_, 2);
v_needlePos_155_ = lean_ctor_get(v_a_106_, 3);
v_isSharedCheck_216_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_216_ == 0)
{
v___x_157_ = v_a_106_;
v_isShared_158_ = v_isSharedCheck_216_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_needlePos_155_);
lean_inc(v_stackPos_154_);
lean_inc(v_table_153_);
lean_inc(v_needle_152_);
lean_dec(v_a_106_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_216_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_str_159_; lean_object* v_startInclusive_160_; lean_object* v_endExclusive_161_; lean_object* v_str_162_; lean_object* v_startInclusive_163_; lean_object* v_endExclusive_164_; lean_object* v_basePos_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_159_ = lean_ctor_get(v_needle_152_, 0);
v_startInclusive_160_ = lean_ctor_get(v_needle_152_, 1);
v_endExclusive_161_ = lean_ctor_get(v_needle_152_, 2);
v_str_162_ = lean_ctor_get(v_s_104_, 0);
v_startInclusive_163_ = lean_ctor_get(v_s_104_, 1);
v_endExclusive_164_ = lean_ctor_get(v_s_104_, 2);
v_basePos_165_ = lean_nat_sub(v_stackPos_154_, v_needlePos_155_);
v___x_166_ = lean_nat_sub(v_endExclusive_161_, v_startInclusive_160_);
v___x_167_ = lean_nat_add(v_basePos_165_, v___x_166_);
v___x_168_ = lean_nat_sub(v_endExclusive_164_, v_startInclusive_163_);
v___x_169_ = lean_nat_dec_le(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
lean_dec(v___x_166_);
lean_del_object(v___x_157_);
lean_dec(v_needlePos_155_);
lean_dec(v_stackPos_154_);
lean_dec_ref(v_table_153_);
lean_dec_ref(v_needle_152_);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_basePos_165_, v___x_170_);
v___x_172_ = lean_nat_dec_le(v___x_171_, v___x_168_);
lean_dec(v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v_basePos_165_);
lean_dec_ref(v_s_104_);
return v_b_107_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_String_Slice_pos_x21(v_s_104_, v_basePos_165_);
lean_dec(v_basePos_165_);
v___x_174_ = lean_box(3);
v_it_109_ = v___x_174_;
v_startPos_110_ = v___x_173_;
v_endPos_111_ = v___x_168_;
goto v___jp_108_;
}
}
else
{
lean_object* v___x_175_; uint8_t v_stackByte_176_; lean_object* v___x_177_; uint8_t v_patByte_178_; uint8_t v___x_179_; 
lean_dec(v___x_168_);
v___x_175_ = lean_nat_add(v_startInclusive_163_, v_stackPos_154_);
v_stackByte_176_ = lean_string_get_byte_fast(v_str_162_, v___x_175_);
v___x_177_ = lean_nat_add(v_startInclusive_160_, v_needlePos_155_);
v_patByte_178_ = lean_string_get_byte_fast(v_str_159_, v___x_177_);
v___x_179_ = lean_uint8_dec_eq(v_stackByte_176_, v_patByte_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v_decide_181_; 
lean_dec(v___x_166_);
v___x_180_ = lean_unsigned_to_nat(0u);
v_decide_181_ = lean_nat_dec_eq(v_needlePos_155_, v___x_180_);
if (v_decide_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_newNeedlePos_184_; uint8_t v___x_185_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_sub(v_needlePos_155_, v___x_182_);
lean_dec(v_needlePos_155_);
v_newNeedlePos_184_ = lean_array_fget_borrowed(v_table_153_, v___x_183_);
lean_dec(v___x_183_);
v___x_185_ = lean_nat_dec_eq(v_newNeedlePos_184_, v___x_180_);
if (v___x_185_ == 0)
{
lean_object* v_oldBasePos_186_; lean_object* v___x_187_; lean_object* v_newBasePos_188_; lean_object* v___x_190_; 
lean_inc(v_newNeedlePos_184_);
v_oldBasePos_186_ = l_String_Slice_pos_x21(v_s_104_, v_basePos_165_);
lean_dec(v_basePos_165_);
v___x_187_ = lean_nat_sub(v_stackPos_154_, v_newNeedlePos_184_);
v_newBasePos_188_ = l_String_Slice_pos_x21(v_s_104_, v___x_187_);
lean_dec(v___x_187_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 3, v_newNeedlePos_184_);
v___x_190_ = v___x_157_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_needle_152_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_table_153_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_stackPos_154_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_newNeedlePos_184_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v_it_109_ = v___x_190_;
v_startPos_110_ = v_oldBasePos_186_;
v_endPos_111_ = v_newBasePos_188_;
goto v___jp_108_;
}
}
else
{
lean_object* v_basePos_192_; lean_object* v_nextStackPos_193_; lean_object* v___x_195_; 
v_basePos_192_ = l_String_Slice_pos_x21(v_s_104_, v_basePos_165_);
lean_dec(v_basePos_165_);
v_nextStackPos_193_ = l_String_Slice_posGE___redArg(v_s_104_, v_stackPos_154_);
lean_inc(v_nextStackPos_193_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 3, v___x_180_);
lean_ctor_set(v___x_157_, 2, v_nextStackPos_193_);
v___x_195_ = v___x_157_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_needle_152_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_table_153_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_nextStackPos_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v___x_180_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v_it_109_ = v___x_195_;
v_startPos_110_ = v_basePos_192_;
v_endPos_111_ = v_nextStackPos_193_;
goto v___jp_108_;
}
}
}
else
{
lean_object* v_basePos_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_nextStackPos_200_; lean_object* v___x_202_; 
lean_dec(v_basePos_165_);
lean_dec(v_needlePos_155_);
v_basePos_197_ = l_String_Slice_pos_x21(v_s_104_, v_stackPos_154_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_stackPos_154_, v___x_198_);
lean_dec(v_stackPos_154_);
v_nextStackPos_200_ = l_String_Slice_posGE___redArg(v_s_104_, v___x_199_);
lean_inc(v_nextStackPos_200_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 3, v___x_180_);
lean_ctor_set(v___x_157_, 2, v_nextStackPos_200_);
v___x_202_ = v___x_157_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_needle_152_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_table_153_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_nextStackPos_200_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___x_180_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
v_it_109_ = v___x_202_;
v_startPos_110_ = v_basePos_197_;
v_endPos_111_ = v_nextStackPos_200_;
goto v___jp_108_;
}
}
}
else
{
lean_object* v___x_204_; lean_object* v_nextStackPos_205_; lean_object* v_nextNeedlePos_206_; uint8_t v_decide_207_; 
lean_dec(v_basePos_165_);
v___x_204_ = lean_unsigned_to_nat(1u);
v_nextStackPos_205_ = lean_nat_add(v_stackPos_154_, v___x_204_);
lean_dec(v_stackPos_154_);
v_nextNeedlePos_206_ = lean_nat_add(v_needlePos_155_, v___x_204_);
lean_dec(v_needlePos_155_);
v_decide_207_ = lean_nat_dec_eq(v_nextNeedlePos_206_, v___x_166_);
lean_dec(v___x_166_);
if (v_decide_207_ == 0)
{
lean_object* v___x_209_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 3, v_nextNeedlePos_206_);
lean_ctor_set(v___x_157_, 2, v_nextStackPos_205_);
v___x_209_ = v___x_157_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_needle_152_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_table_153_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_nextStackPos_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_nextNeedlePos_206_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
v_a_106_ = v___x_209_;
goto _start;
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec(v_nextNeedlePos_206_);
v___x_212_ = lean_unsigned_to_nat(0u);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 3, v___x_212_);
lean_ctor_set(v___x_157_, 2, v_nextStackPos_205_);
v___x_214_ = v___x_157_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_needle_152_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_table_153_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_nextStackPos_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v_it_120_ = v___x_214_;
goto v___jp_119_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_104_);
return v_b_107_;
}
}
v___jp_108_:
{
lean_object* v___x_112_; lean_object* v_str_113_; lean_object* v_startInclusive_114_; lean_object* v_endExclusive_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v_s_104_);
v___x_112_ = l_String_Slice_slice_x21(v_s_104_, v_startPos_110_, v_endPos_111_);
lean_dec(v_endPos_111_);
lean_dec(v_startPos_110_);
v_str_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_str_113_);
v_startInclusive_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_startInclusive_114_);
v_endExclusive_115_ = lean_ctor_get(v___x_112_, 2);
lean_inc(v_endExclusive_115_);
lean_dec_ref(v___x_112_);
v___x_116_ = lean_string_utf8_extract_fast(v_str_113_, v_startInclusive_114_, v_endExclusive_115_);
lean_dec(v_endExclusive_115_);
lean_dec(v_startInclusive_114_);
lean_dec_ref(v_str_113_);
v___x_117_ = lean_string_append(v_b_107_, v___x_116_);
lean_dec_ref(v___x_116_);
v_a_106_ = v_it_109_;
v_b_107_ = v___x_117_;
goto _start;
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_string_utf8_byte_size(v_replacement_105_);
v___x_123_ = lean_string_utf8_extract_fast(v_replacement_105_, v___x_121_, v___x_122_);
v___x_124_ = lean_string_append(v_b_107_, v___x_123_);
lean_dec_ref(v___x_123_);
v_a_106_ = v_it_120_;
v_b_107_ = v___x_124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* v_s_217_, lean_object* v_replacement_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_217_, v_replacement_218_, v_a_219_, v_b_220_);
lean_dec_ref(v_replacement_218_);
return v_res_221_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_225_ = lean_string_utf8_byte_size(v___x_224_);
return v___x_225_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_228_ = lean_nat_dec_eq(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_234_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
v___x_237_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_238_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
lean_ctor_set(v___x_238_, 3, v___x_235_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* v_s_241_, lean_object* v_replacement_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
v___x_244_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_241_, v_replacement_242_, v___x_245_, v___x_243_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7));
v___x_248_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_241_, v_replacement_242_, v___x_247_, v___x_243_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* v_s_249_, lean_object* v_replacement_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_249_, v_replacement_250_);
lean_dec_ref(v_replacement_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* v_leanSysroot_252_, size_t v_sz_253_, size_t v_i_254_, lean_object* v_bs_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_usize_dec_lt(v_i_254_, v_sz_253_);
if (v___x_256_ == 0)
{
return v_bs_255_;
}
else
{
lean_object* v_v_257_; lean_object* v___x_258_; lean_object* v_bs_x27_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v_v_257_ = lean_array_uget(v_bs_255_, v_i_254_);
v___x_258_ = lean_unsigned_to_nat(0u);
v_bs_x27_259_ = lean_array_uset(v_bs_255_, v_i_254_, v___x_258_);
v___x_260_ = lean_string_utf8_byte_size(v_v_257_);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v_v_257_);
lean_ctor_set(v___x_261_, 1, v___x_258_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_261_, v_leanSysroot_252_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_254_, v___x_263_);
v___x_265_ = lean_array_uset(v_bs_x27_259_, v_i_254_, v___x_262_);
v_i_254_ = v___x_264_;
v_bs_255_ = v___x_265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* v_leanSysroot_267_, lean_object* v_sz_268_, lean_object* v_i_269_, lean_object* v_bs_270_){
_start:
{
size_t v_sz_boxed_271_; size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_sz_boxed_271_ = lean_unbox_usize(v_sz_268_);
lean_dec(v_sz_268_);
v_i_boxed_272_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_267_, v_sz_boxed_271_, v_i_boxed_272_, v_bs_270_);
lean_dec_ref(v_leanSysroot_267_);
return v_res_273_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_box(0);
v___x_275_ = lean_get_leanc_internal_flags(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__0, &l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
v___x_277_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_276_);
return v___x_277_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2(void){
_start:
{
lean_object* v___x_278_; size_t v_sz_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_279_ = lean_array_size(v___x_278_);
return v_sz_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* v_leanSysroot_280_){
_start:
{
lean_object* v___x_281_; size_t v_sz_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_281_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_282_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__2, &l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_280_, v_sz_282_, v___x_283_, v___x_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* v_leanSysroot_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_285_);
lean_dec_ref(v_leanSysroot_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* v_s_287_, lean_object* v_pattern_288_, lean_object* v_replacement_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_287_, v_replacement_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* v_s_291_, lean_object* v_pattern_292_, lean_object* v_replacement_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(v_s_291_, v_pattern_292_, v_replacement_293_);
lean_dec_ref(v_replacement_293_);
lean_dec_ref(v_pattern_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* v_s_295_, lean_object* v_replacement_296_, lean_object* v_inst_297_, lean_object* v_R_298_, lean_object* v_a_299_, lean_object* v_b_300_, lean_object* v_c_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_295_, v_replacement_296_, v_a_299_, v_b_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* v_s_303_, lean_object* v_replacement_304_, lean_object* v_inst_305_, lean_object* v_R_306_, lean_object* v_a_307_, lean_object* v_b_308_, lean_object* v_c_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_303_, v_replacement_304_, v_inst_305_, v_R_306_, v_a_307_, v_b_308_, v_c_309_);
lean_dec_ref(v_replacement_304_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* v_linkStatic_312_){
_start:
{
uint8_t v_linkStatic_boxed_313_; lean_object* v_res_314_; 
v_linkStatic_boxed_313_ = lean_unbox(v_linkStatic_312_);
v_res_314_ = lean_get_linker_flags(v_linkStatic_boxed_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t v_linkStatic_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_get_linker_flags(v_linkStatic_315_);
v___x_317_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* v_linkStatic_318_){
_start:
{
uint8_t v_linkStatic_boxed_319_; lean_object* v_res_320_; 
v_linkStatic_boxed_319_ = lean_unbox(v_linkStatic_318_);
v_res_320_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_boxed_319_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__0));
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_array_push(v___x_326_, v___x_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* v_leanSysroot_328_, uint8_t v_linkStatic_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_330_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__1));
v___x_331_ = l_System_FilePath_join(v_leanSysroot_328_, v___x_330_);
v___x_332_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__2));
v___x_333_ = l_System_FilePath_join(v___x_331_, v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_Compiler_FFI_getLinkerFlags___closed__3, &l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once, _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
v___x_335_ = lean_array_push(v___x_334_, v___x_333_);
v___x_336_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_329_);
v___x_337_ = l_Array_append___redArg(v___x_335_, v___x_336_);
lean_dec_ref(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* v_leanSysroot_338_, lean_object* v_linkStatic_339_){
_start:
{
uint8_t v_linkStatic_boxed_340_; lean_object* v_res_341_; 
v_linkStatic_boxed_340_ = lean_unbox(v_linkStatic_339_);
v_res_341_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_338_, v_linkStatic_boxed_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* v_a_00___x40___internal___hyg_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_343_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_get_internal_linker_flags(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
v___x_348_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_347_);
return v___x_348_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2(void){
_start:
{
lean_object* v___x_349_; size_t v_sz_350_; 
v___x_349_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_350_ = lean_array_size(v___x_349_);
return v_sz_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* v_leanSysroot_351_){
_start:
{
lean_object* v___x_352_; size_t v_sz_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_353_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_351_, v_sz_353_, v___x_354_, v___x_352_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* v_leanSysroot_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_356_);
lean_dec_ref(v_leanSysroot_356_);
return v_res_357_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
