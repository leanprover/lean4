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
lean_object* v_currPos_27_; lean_object* v_searcher_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_54_; 
v_currPos_27_ = lean_ctor_get(v_a_13_, 0);
v_searcher_28_ = lean_ctor_get(v_a_13_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_54_ == 0)
{
v___x_30_ = v_a_13_;
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_searcher_28_);
lean_inc(v_currPos_27_);
lean_dec(v_a_13_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_startInclusive_32_; lean_object* v_endExclusive_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_startInclusive_32_ = lean_ctor_get(v___x_11_, 1);
v_endExclusive_33_ = lean_ctor_get(v___x_11_, 2);
v___x_34_ = lean_nat_sub(v_endExclusive_33_, v_startInclusive_32_);
v___x_35_ = lean_nat_dec_eq(v_searcher_28_, v___x_34_);
lean_dec(v___x_34_);
if (v___x_35_ == 0)
{
uint32_t v___x_36_; uint32_t v___x_37_; uint8_t v___x_38_; 
v___x_36_ = 32;
v___x_37_ = lean_string_utf8_get_fast(v_s_10_, v_searcher_28_);
v___x_38_ = lean_uint32_dec_eq(v___x_37_, v___x_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_28_);
lean_dec(v_searcher_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_currPos_27_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_43_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
v_a_13_ = v___x_41_;
goto _start;
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_slice_47_; lean_object* v_nextIt_49_; 
v___x_44_ = lean_string_utf8_next_fast(v_s_10_, v_searcher_28_);
v___x_45_ = lean_nat_sub(v___x_44_, v_searcher_28_);
v___x_46_ = lean_nat_add(v_searcher_28_, v___x_45_);
lean_dec(v___x_45_);
v_slice_47_ = l_String_Slice_subslice_x21(v___x_11_, v_currPos_27_, v_searcher_28_);
lean_inc(v___x_46_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_46_);
lean_ctor_set(v___x_30_, 0, v___x_46_);
v_nextIt_49_ = v___x_30_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_46_);
v_nextIt_49_ = v_reuseFailAlloc_52_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v_startInclusive_50_; lean_object* v_endExclusive_51_; 
v_startInclusive_50_ = lean_ctor_get(v_slice_47_, 0);
lean_inc(v_startInclusive_50_);
v_endExclusive_51_ = lean_ctor_get(v_slice_47_, 1);
lean_inc(v_endExclusive_51_);
lean_dec_ref(v_slice_47_);
v_it_16_ = v_nextIt_49_;
v_startInclusive_17_ = v_startInclusive_50_;
v_endExclusive_18_ = v_endExclusive_51_;
goto v___jp_15_;
}
}
}
else
{
lean_object* v___x_53_; 
lean_del_object(v___x_30_);
lean_dec(v_searcher_28_);
v___x_53_ = lean_box(1);
lean_inc(v___x_12_);
v_it_16_ = v___x_53_;
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
lean_dec_ref(v___x_22_);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* v_s_55_, lean_object* v___x_56_, lean_object* v___x_57_, lean_object* v_a_58_, lean_object* v_b_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_55_, v___x_56_, v___x_57_, v_a_58_, v_b_59_);
lean_dec_ref(v___x_56_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_string_utf8_byte_size(v_s_63_);
lean_inc_ref(v_s_63_);
v___x_66_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_66_, 0, v_s_63_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_65_);
v___x_67_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v___x_66_);
v___x_68_ = ((lean_object*)(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0));
v___x_69_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_63_, v___x_66_, v___x_65_, v___x_67_, v___x_68_);
lean_dec_ref(v___x_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* v_s_70_, lean_object* v___x_71_, lean_object* v___x_72_, lean_object* v_inst_73_, lean_object* v_R_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_70_, v___x_71_, v___x_72_, v_a_75_, v_b_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* v_s_78_, lean_object* v___x_79_, lean_object* v___x_80_, lean_object* v_inst_81_, lean_object* v_R_82_, lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_78_, v___x_79_, v___x_80_, v_inst_81_, v_R_82_, v_a_83_, v_b_84_);
lean_dec_ref(v___x_79_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_box(0);
v___x_87_ = lean_get_leanc_extra_flags(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__0, &l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
v___x_89_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__1, &l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
v___x_94_ = lean_unsigned_to_nat(2u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_array_push(v___x_95_, v___x_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* v_leanSysroot_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
v___x_99_ = l_System_FilePath_join(v_leanSysroot_97_, v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags___closed__2, &l_Lean_Compiler_FFI_getCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getCFlags___closed__2);
v___x_101_ = lean_array_push(v___x_100_, v___x_99_);
v___x_102_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_103_ = l_Array_append___redArg(v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* v_a_00___x40___internal___hyg_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* v_s_107_, lean_object* v_replacement_108_, lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
lean_object* v_it_112_; lean_object* v_startPos_113_; lean_object* v_endPos_114_; lean_object* v_it_123_; 
switch(lean_obj_tag(v_a_109_))
{
case 0:
{
lean_object* v_pos_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_141_; 
v_pos_129_ = lean_ctor_get(v_a_109_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_141_ == 0)
{
v___x_131_ = v_a_109_;
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_pos_129_);
lean_dec(v_a_109_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_startInclusive_133_; lean_object* v_endExclusive_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_startInclusive_133_ = lean_ctor_get(v_s_107_, 1);
v_endExclusive_134_ = lean_ctor_get(v_s_107_, 2);
v___x_135_ = lean_nat_sub(v_endExclusive_134_, v_startInclusive_133_);
v___x_136_ = lean_nat_dec_eq(v_pos_129_, v___x_135_);
lean_dec(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
v___x_138_ = v___x_131_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_pos_129_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v_it_123_ = v___x_138_;
goto v___jp_122_;
}
}
else
{
lean_object* v___x_140_; 
lean_del_object(v___x_131_);
lean_dec(v_pos_129_);
v___x_140_ = lean_box(3);
v_it_123_ = v___x_140_;
goto v___jp_122_;
}
}
}
case 1:
{
lean_object* v_pos_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_154_; 
v_pos_142_ = lean_ctor_get(v_a_109_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_154_ == 0)
{
v___x_144_ = v_a_109_;
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_pos_142_);
lean_dec(v_a_109_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_str_146_; lean_object* v_startInclusive_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v_str_146_ = lean_ctor_get(v_s_107_, 0);
v_startInclusive_147_ = lean_ctor_get(v_s_107_, 1);
v___x_148_ = lean_nat_add(v_startInclusive_147_, v_pos_142_);
v___x_149_ = lean_string_utf8_next_fast(v_str_146_, v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = lean_nat_sub(v___x_149_, v_startInclusive_147_);
lean_inc(v___x_150_);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 0);
lean_ctor_set(v___x_144_, 0, v___x_150_);
v___x_152_ = v___x_144_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v_it_112_ = v___x_152_;
v_startPos_113_ = v_pos_142_;
v_endPos_114_ = v___x_150_;
goto v___jp_111_;
}
}
}
case 2:
{
lean_object* v_needle_155_; lean_object* v_table_156_; lean_object* v_stackPos_157_; lean_object* v_needlePos_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_217_; 
v_needle_155_ = lean_ctor_get(v_a_109_, 0);
v_table_156_ = lean_ctor_get(v_a_109_, 1);
v_stackPos_157_ = lean_ctor_get(v_a_109_, 2);
v_needlePos_158_ = lean_ctor_get(v_a_109_, 3);
v_isSharedCheck_217_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_217_ == 0)
{
v___x_160_ = v_a_109_;
v_isShared_161_ = v_isSharedCheck_217_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_needlePos_158_);
lean_inc(v_stackPos_157_);
lean_inc(v_table_156_);
lean_inc(v_needle_155_);
lean_dec(v_a_109_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_217_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_str_162_; lean_object* v_startInclusive_163_; lean_object* v_endExclusive_164_; lean_object* v_str_165_; lean_object* v_startInclusive_166_; lean_object* v_endExclusive_167_; lean_object* v_basePos_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_str_162_ = lean_ctor_get(v_needle_155_, 0);
v_startInclusive_163_ = lean_ctor_get(v_needle_155_, 1);
v_endExclusive_164_ = lean_ctor_get(v_needle_155_, 2);
v_str_165_ = lean_ctor_get(v_s_107_, 0);
v_startInclusive_166_ = lean_ctor_get(v_s_107_, 1);
v_endExclusive_167_ = lean_ctor_get(v_s_107_, 2);
v_basePos_168_ = lean_nat_sub(v_stackPos_157_, v_needlePos_158_);
v___x_169_ = lean_nat_sub(v_endExclusive_164_, v_startInclusive_163_);
v___x_170_ = lean_nat_add(v_basePos_168_, v___x_169_);
v___x_171_ = lean_nat_sub(v_endExclusive_167_, v_startInclusive_166_);
v___x_172_ = lean_nat_dec_le(v___x_170_, v___x_171_);
lean_dec(v___x_170_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
lean_dec(v___x_169_);
lean_del_object(v___x_160_);
lean_dec(v_needlePos_158_);
lean_dec(v_stackPos_157_);
lean_dec_ref(v_table_156_);
lean_dec_ref(v_needle_155_);
v___x_173_ = lean_nat_dec_lt(v_basePos_168_, v___x_171_);
if (v___x_173_ == 0)
{
lean_dec(v___x_171_);
lean_dec(v_basePos_168_);
lean_dec_ref(v_s_107_);
return v_b_110_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_String_Slice_pos_x21(v_s_107_, v_basePos_168_);
lean_dec(v_basePos_168_);
v___x_175_ = lean_box(3);
v_it_112_ = v___x_175_;
v_startPos_113_ = v___x_174_;
v_endPos_114_ = v___x_171_;
goto v___jp_111_;
}
}
else
{
lean_object* v___x_176_; uint8_t v_stackByte_177_; lean_object* v___x_178_; uint8_t v_patByte_179_; uint8_t v___x_180_; 
lean_dec(v___x_171_);
v___x_176_ = lean_nat_add(v_startInclusive_166_, v_stackPos_157_);
v_stackByte_177_ = lean_string_get_byte_fast(v_str_165_, v___x_176_);
v___x_178_ = lean_nat_add(v_startInclusive_163_, v_needlePos_158_);
v_patByte_179_ = lean_string_get_byte_fast(v_str_162_, v___x_178_);
v___x_180_ = lean_uint8_dec_eq(v_stackByte_177_, v_patByte_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
lean_dec(v___x_169_);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_nat_dec_eq(v_needlePos_158_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_newNeedlePos_185_; uint8_t v___x_186_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v_needlePos_158_, v___x_183_);
lean_dec(v_needlePos_158_);
v_newNeedlePos_185_ = lean_array_fget_borrowed(v_table_156_, v___x_184_);
lean_dec(v___x_184_);
v___x_186_ = lean_nat_dec_eq(v_newNeedlePos_185_, v___x_181_);
if (v___x_186_ == 0)
{
lean_object* v_oldBasePos_187_; lean_object* v___x_188_; lean_object* v_newBasePos_189_; lean_object* v___x_191_; 
lean_inc(v_newNeedlePos_185_);
v_oldBasePos_187_ = l_String_Slice_pos_x21(v_s_107_, v_basePos_168_);
lean_dec(v_basePos_168_);
v___x_188_ = lean_nat_sub(v_stackPos_157_, v_newNeedlePos_185_);
v_newBasePos_189_ = l_String_Slice_pos_x21(v_s_107_, v___x_188_);
lean_dec(v___x_188_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v_newNeedlePos_185_);
v___x_191_ = v___x_160_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_needle_155_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_table_156_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_stackPos_157_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_newNeedlePos_185_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
v_it_112_ = v___x_191_;
v_startPos_113_ = v_oldBasePos_187_;
v_endPos_114_ = v_newBasePos_189_;
goto v___jp_111_;
}
}
else
{
lean_object* v_basePos_193_; lean_object* v_nextStackPos_194_; lean_object* v___x_196_; 
v_basePos_193_ = l_String_Slice_pos_x21(v_s_107_, v_basePos_168_);
lean_dec(v_basePos_168_);
v_nextStackPos_194_ = l_String_Slice_posGE___redArg(v_s_107_, v_stackPos_157_);
lean_inc(v_nextStackPos_194_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v___x_181_);
lean_ctor_set(v___x_160_, 2, v_nextStackPos_194_);
v___x_196_ = v___x_160_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_needle_155_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_table_156_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_nextStackPos_194_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___x_181_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
v_it_112_ = v___x_196_;
v_startPos_113_ = v_basePos_193_;
v_endPos_114_ = v_nextStackPos_194_;
goto v___jp_111_;
}
}
}
else
{
lean_object* v_basePos_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_nextStackPos_201_; lean_object* v___x_203_; 
lean_dec(v_basePos_168_);
lean_dec(v_needlePos_158_);
v_basePos_198_ = l_String_Slice_pos_x21(v_s_107_, v_stackPos_157_);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_stackPos_157_, v___x_199_);
lean_dec(v_stackPos_157_);
v_nextStackPos_201_ = l_String_Slice_posGE___redArg(v_s_107_, v___x_200_);
lean_inc(v_nextStackPos_201_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v___x_181_);
lean_ctor_set(v___x_160_, 2, v_nextStackPos_201_);
v___x_203_ = v___x_160_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_needle_155_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_table_156_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_nextStackPos_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___x_181_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_it_112_ = v___x_203_;
v_startPos_113_ = v_basePos_198_;
v_endPos_114_ = v_nextStackPos_201_;
goto v___jp_111_;
}
}
}
else
{
lean_object* v___x_205_; lean_object* v_nextStackPos_206_; lean_object* v_nextNeedlePos_207_; uint8_t v___x_208_; 
lean_dec(v_basePos_168_);
v___x_205_ = lean_unsigned_to_nat(1u);
v_nextStackPos_206_ = lean_nat_add(v_stackPos_157_, v___x_205_);
lean_dec(v_stackPos_157_);
v_nextNeedlePos_207_ = lean_nat_add(v_needlePos_158_, v___x_205_);
lean_dec(v_needlePos_158_);
v___x_208_ = lean_nat_dec_eq(v_nextNeedlePos_207_, v___x_169_);
lean_dec(v___x_169_);
if (v___x_208_ == 0)
{
lean_object* v___x_210_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v_nextNeedlePos_207_);
lean_ctor_set(v___x_160_, 2, v_nextStackPos_206_);
v___x_210_ = v___x_160_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_needle_155_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_table_156_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_nextStackPos_206_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_nextNeedlePos_207_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_a_109_ = v___x_210_;
goto _start;
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v_nextNeedlePos_207_);
v___x_213_ = lean_unsigned_to_nat(0u);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v___x_213_);
lean_ctor_set(v___x_160_, 2, v_nextStackPos_206_);
v___x_215_ = v___x_160_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_needle_155_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_table_156_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_nextStackPos_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_it_123_ = v___x_215_;
goto v___jp_122_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_107_);
return v_b_110_;
}
}
v___jp_111_:
{
lean_object* v___x_115_; lean_object* v_str_116_; lean_object* v_startInclusive_117_; lean_object* v_endExclusive_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_inc_ref(v_s_107_);
v___x_115_ = l_String_Slice_slice_x21(v_s_107_, v_startPos_113_, v_endPos_114_);
lean_dec(v_endPos_114_);
lean_dec(v_startPos_113_);
v_str_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_str_116_);
v_startInclusive_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_startInclusive_117_);
v_endExclusive_118_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_endExclusive_118_);
lean_dec_ref(v___x_115_);
v___x_119_ = lean_string_utf8_extract(v_str_116_, v_startInclusive_117_, v_endExclusive_118_);
lean_dec(v_endExclusive_118_);
lean_dec(v_startInclusive_117_);
lean_dec_ref(v_str_116_);
v___x_120_ = lean_string_append(v_b_110_, v___x_119_);
lean_dec_ref(v___x_119_);
v_a_109_ = v_it_112_;
v_b_110_ = v___x_120_;
goto _start;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_string_utf8_byte_size(v_replacement_108_);
v___x_126_ = lean_string_utf8_extract(v_replacement_108_, v___x_124_, v___x_125_);
v___x_127_ = lean_string_append(v_b_110_, v___x_126_);
lean_dec_ref(v___x_126_);
v_a_109_ = v_it_123_;
v_b_110_ = v___x_127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* v_s_218_, lean_object* v_replacement_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_218_, v_replacement_219_, v_a_220_, v_b_221_);
lean_dec_ref(v_replacement_219_);
return v_res_222_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_226_ = lean_string_utf8_byte_size(v___x_225_);
return v___x_226_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_229_ = lean_nat_dec_eq(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_230_);
return v___x_233_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_235_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
v___x_238_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_239_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
lean_ctor_set(v___x_239_, 3, v___x_236_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* v_s_242_, lean_object* v_replacement_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
v___x_245_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
v___x_247_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_242_, v_replacement_243_, v___x_246_, v___x_244_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7));
v___x_249_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_242_, v_replacement_243_, v___x_248_, v___x_244_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* v_s_250_, lean_object* v_replacement_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_250_, v_replacement_251_);
lean_dec_ref(v_replacement_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* v_leanSysroot_253_, size_t v_sz_254_, size_t v_i_255_, lean_object* v_bs_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_lt(v_i_255_, v_sz_254_);
if (v___x_257_ == 0)
{
return v_bs_256_;
}
else
{
lean_object* v_v_258_; lean_object* v___x_259_; lean_object* v_bs_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
v_v_258_ = lean_array_uget(v_bs_256_, v_i_255_);
v___x_259_ = lean_unsigned_to_nat(0u);
v_bs_x27_260_ = lean_array_uset(v_bs_256_, v_i_255_, v___x_259_);
v___x_261_ = lean_string_utf8_byte_size(v_v_258_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v_v_258_);
lean_ctor_set(v___x_262_, 1, v___x_259_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_262_, v_leanSysroot_253_);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_255_, v___x_264_);
v___x_266_ = lean_array_uset(v_bs_x27_260_, v_i_255_, v___x_263_);
v_i_255_ = v___x_265_;
v_bs_256_ = v___x_266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* v_leanSysroot_268_, lean_object* v_sz_269_, lean_object* v_i_270_, lean_object* v_bs_271_){
_start:
{
size_t v_sz_boxed_272_; size_t v_i_boxed_273_; lean_object* v_res_274_; 
v_sz_boxed_272_ = lean_unbox_usize(v_sz_269_);
lean_dec(v_sz_269_);
v_i_boxed_273_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_268_, v_sz_boxed_272_, v_i_boxed_273_, v_bs_271_);
lean_dec_ref(v_leanSysroot_268_);
return v_res_274_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(0);
v___x_276_ = lean_get_leanc_internal_flags(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__0, &l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
v___x_278_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_277_);
return v___x_278_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2(void){
_start:
{
lean_object* v___x_279_; size_t v_sz_280_; 
v___x_279_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_280_ = lean_array_size(v___x_279_);
return v_sz_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* v_leanSysroot_281_){
_start:
{
lean_object* v___x_282_; size_t v_sz_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_283_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__2, &l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
v___x_284_ = ((size_t)0ULL);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_281_, v_sz_283_, v___x_284_, v___x_282_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* v_leanSysroot_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_286_);
lean_dec_ref(v_leanSysroot_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* v_s_288_, lean_object* v_pattern_289_, lean_object* v_replacement_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_288_, v_replacement_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* v_s_292_, lean_object* v_pattern_293_, lean_object* v_replacement_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(v_s_292_, v_pattern_293_, v_replacement_294_);
lean_dec_ref(v_replacement_294_);
lean_dec_ref(v_pattern_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* v_s_296_, lean_object* v_replacement_297_, lean_object* v_inst_298_, lean_object* v_R_299_, lean_object* v_a_300_, lean_object* v_b_301_, lean_object* v_c_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_296_, v_replacement_297_, v_a_300_, v_b_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* v_s_304_, lean_object* v_replacement_305_, lean_object* v_inst_306_, lean_object* v_R_307_, lean_object* v_a_308_, lean_object* v_b_309_, lean_object* v_c_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_304_, v_replacement_305_, v_inst_306_, v_R_307_, v_a_308_, v_b_309_, v_c_310_);
lean_dec_ref(v_replacement_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* v_linkStatic_313_){
_start:
{
uint8_t v_linkStatic_boxed_314_; lean_object* v_res_315_; 
v_linkStatic_boxed_314_ = lean_unbox(v_linkStatic_313_);
v_res_315_ = lean_get_linker_flags(v_linkStatic_boxed_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t v_linkStatic_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_get_linker_flags(v_linkStatic_316_);
v___x_318_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* v_linkStatic_319_){
_start:
{
uint8_t v_linkStatic_boxed_320_; lean_object* v_res_321_; 
v_linkStatic_boxed_320_ = lean_unbox(v_linkStatic_319_);
v_res_321_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_boxed_320_);
return v_res_321_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__0));
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_array_push(v___x_327_, v___x_325_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* v_leanSysroot_329_, uint8_t v_linkStatic_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_331_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__1));
v___x_332_ = l_System_FilePath_join(v_leanSysroot_329_, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__2));
v___x_334_ = l_System_FilePath_join(v___x_332_, v___x_333_);
v___x_335_ = lean_obj_once(&l_Lean_Compiler_FFI_getLinkerFlags___closed__3, &l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once, _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
v___x_337_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_330_);
v___x_338_ = l_Array_append___redArg(v___x_336_, v___x_337_);
lean_dec_ref(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* v_leanSysroot_339_, lean_object* v_linkStatic_340_){
_start:
{
uint8_t v_linkStatic_boxed_341_; lean_object* v_res_342_; 
v_linkStatic_boxed_341_ = lean_unbox(v_linkStatic_340_);
v_res_342_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_339_, v_linkStatic_boxed_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* v_a_00___x40___internal___hyg_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_344_);
return v_res_345_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_get_internal_linker_flags(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
v___x_349_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_348_);
return v___x_349_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2(void){
_start:
{
lean_object* v___x_350_; size_t v_sz_351_; 
v___x_350_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_351_ = lean_array_size(v___x_350_);
return v_sz_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* v_leanSysroot_352_){
_start:
{
lean_object* v___x_353_; size_t v_sz_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_354_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_352_, v_sz_354_, v___x_355_, v___x_353_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* v_leanSysroot_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_357_);
lean_dec_ref(v_leanSysroot_357_);
return v_res_358_;
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
