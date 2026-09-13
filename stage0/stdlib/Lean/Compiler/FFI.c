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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___closed__0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
return v_res_9_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v_s_13_);
lean_dec_ref(v_s_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object* v_s_15_, lean_object* v___x_16_, lean_object* v___x_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
lean_object* v_it_21_; lean_object* v_startInclusive_22_; lean_object* v_endExclusive_23_; 
if (lean_obj_tag(v_a_18_) == 0)
{
lean_object* v_currPos_32_; lean_object* v_searcher_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_56_; 
v_currPos_32_ = lean_ctor_get(v_a_18_, 0);
v_searcher_33_ = lean_ctor_get(v_a_18_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_a_18_);
if (v_isSharedCheck_56_ == 0)
{
v___x_35_ = v_a_18_;
v_isShared_36_ = v_isSharedCheck_56_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_searcher_33_);
lean_inc(v_currPos_32_);
lean_dec(v_a_18_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_56_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
uint8_t v_decide_37_; 
v_decide_37_ = lean_nat_dec_eq(v_searcher_33_, v___x_17_);
if (v_decide_37_ == 0)
{
uint32_t v___x_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = 32;
v___x_39_ = lean_string_utf8_get_fast(v_s_15_, v_searcher_33_);
v___x_40_ = lean_uint32_dec_eq(v___x_39_, v___x_38_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = lean_string_utf8_next_fast(v_s_15_, v_searcher_33_);
lean_dec(v_searcher_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_41_);
v___x_43_ = v___x_35_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_currPos_32_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_45_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
v_a_18_ = v___x_43_;
goto _start;
}
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_slice_49_; lean_object* v_nextIt_51_; 
v___x_46_ = lean_string_utf8_next_fast(v_s_15_, v_searcher_33_);
v___x_47_ = lean_nat_sub(v___x_46_, v_searcher_33_);
v___x_48_ = lean_nat_add(v_searcher_33_, v___x_47_);
lean_dec(v___x_47_);
v_slice_49_ = l_String_Slice_subslice_x21(v___x_16_, v_currPos_32_, v_searcher_33_);
lean_inc(v___x_48_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_48_);
lean_ctor_set(v___x_35_, 0, v___x_48_);
v_nextIt_51_ = v___x_35_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_48_);
v_nextIt_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v_startInclusive_52_; lean_object* v_endExclusive_53_; 
v_startInclusive_52_ = lean_ctor_get(v_slice_49_, 0);
lean_inc(v_startInclusive_52_);
v_endExclusive_53_ = lean_ctor_get(v_slice_49_, 1);
lean_inc(v_endExclusive_53_);
lean_dec_ref(v_slice_49_);
v_it_21_ = v_nextIt_51_;
v_startInclusive_22_ = v_startInclusive_52_;
v_endExclusive_23_ = v_endExclusive_53_;
goto v___jp_20_;
}
}
}
else
{
lean_object* v___x_55_; 
lean_del_object(v___x_35_);
lean_dec(v_searcher_33_);
v___x_55_ = lean_box(1);
lean_inc(v___x_17_);
v_it_21_ = v___x_55_;
v_startInclusive_22_ = v_currPos_32_;
v_endExclusive_23_ = v___x_17_;
goto v___jp_20_;
}
}
}
else
{
lean_dec(v___x_17_);
lean_dec_ref(v_s_15_);
return v_b_19_;
}
v___jp_20_:
{
lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = lean_nat_sub(v_endExclusive_23_, v_startInclusive_22_);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_nat_dec_eq(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_inc_ref(v_s_15_);
v___x_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_27_, 0, v_s_15_);
lean_ctor_set(v___x_27_, 1, v_startInclusive_22_);
lean_ctor_set(v___x_27_, 2, v_endExclusive_23_);
v___x_28_ = l_String_Slice_toString(v___x_27_);
lean_dec_ref_known(v___x_27_, 3);
v___x_29_ = lean_array_push(v_b_19_, v___x_28_);
v_a_18_ = v_it_21_;
v_b_19_ = v___x_29_;
goto _start;
}
else
{
lean_dec(v_endExclusive_23_);
lean_dec(v_startInclusive_22_);
v_a_18_ = v_it_21_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* v_s_57_, lean_object* v___x_58_, lean_object* v___x_59_, lean_object* v_a_60_, lean_object* v_b_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_57_, v___x_58_, v___x_59_, v_a_60_, v_b_61_);
lean_dec_ref(v___x_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* v_s_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_string_utf8_byte_size(v_s_65_);
lean_inc_ref(v_s_65_);
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v_s_65_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_67_);
v___x_69_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
v___x_70_ = ((lean_object*)(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0));
v___x_71_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_65_, v___x_68_, v___x_67_, v___x_69_, v___x_70_);
lean_dec_ref_known(v___x_68_, 3);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* v_s_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_inst_75_, lean_object* v_R_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_72_, v___x_73_, v___x_74_, v_a_77_, v_b_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* v_s_80_, lean_object* v___x_81_, lean_object* v___x_82_, lean_object* v_inst_83_, lean_object* v_R_84_, lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_80_, v___x_81_, v___x_82_, v_inst_83_, v_R_84_, v_a_85_, v_b_86_);
lean_dec_ref(v___x_81_);
return v_res_87_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_get_leanc_extra_flags(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__0, &l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
v___x_91_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__1, &l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_array_push(v___x_97_, v___x_95_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* v_leanSysroot_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_100_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
v___x_101_ = l_System_FilePath_join(v_leanSysroot_99_, v___x_100_);
v___x_102_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags___closed__2, &l_Lean_Compiler_FFI_getCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getCFlags___closed__2);
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
v___x_104_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_105_ = l_Array_append___redArg(v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* v_a_00___x40___internal___hyg_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* v_s_109_, lean_object* v_replacement_110_, lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_it_114_; lean_object* v_startPos_115_; lean_object* v_endPos_116_; lean_object* v_it_125_; 
switch(lean_obj_tag(v_a_111_))
{
case 0:
{
lean_object* v_pos_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_143_; 
v_pos_131_ = lean_ctor_get(v_a_111_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_143_ == 0)
{
v___x_133_ = v_a_111_;
v_isShared_134_ = v_isSharedCheck_143_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_pos_131_);
lean_dec(v_a_111_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_143_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_startInclusive_135_; lean_object* v_endExclusive_136_; lean_object* v___x_137_; uint8_t v_decide_138_; 
v_startInclusive_135_ = lean_ctor_get(v_s_109_, 1);
v_endExclusive_136_ = lean_ctor_get(v_s_109_, 2);
v___x_137_ = lean_nat_sub(v_endExclusive_136_, v_startInclusive_135_);
v_decide_138_ = lean_nat_dec_eq(v_pos_131_, v___x_137_);
lean_dec(v___x_137_);
if (v_decide_138_ == 0)
{
lean_object* v___x_140_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
v___x_140_ = v___x_133_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_pos_131_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_it_125_ = v___x_140_;
goto v___jp_124_;
}
}
else
{
lean_object* v___x_142_; 
lean_del_object(v___x_133_);
lean_dec(v_pos_131_);
v___x_142_ = lean_box(3);
v_it_125_ = v___x_142_;
goto v___jp_124_;
}
}
}
case 1:
{
lean_object* v_pos_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_156_; 
v_pos_144_ = lean_ctor_get(v_a_111_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_156_ == 0)
{
v___x_146_ = v_a_111_;
v_isShared_147_ = v_isSharedCheck_156_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_pos_144_);
lean_dec(v_a_111_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_156_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_str_148_; lean_object* v_startInclusive_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v_str_148_ = lean_ctor_get(v_s_109_, 0);
v_startInclusive_149_ = lean_ctor_get(v_s_109_, 1);
v___x_150_ = lean_nat_add(v_startInclusive_149_, v_pos_144_);
v___x_151_ = lean_string_utf8_next_fast(v_str_148_, v___x_150_);
lean_dec(v___x_150_);
v___x_152_ = lean_nat_sub(v___x_151_, v_startInclusive_149_);
lean_inc(v___x_152_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 0);
lean_ctor_set(v___x_146_, 0, v___x_152_);
v___x_154_ = v___x_146_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
v_it_114_ = v___x_154_;
v_startPos_115_ = v_pos_144_;
v_endPos_116_ = v___x_152_;
goto v___jp_113_;
}
}
}
case 2:
{
lean_object* v_needle_157_; lean_object* v_table_158_; lean_object* v_stackPos_159_; lean_object* v_needlePos_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_221_; 
v_needle_157_ = lean_ctor_get(v_a_111_, 0);
v_table_158_ = lean_ctor_get(v_a_111_, 1);
v_stackPos_159_ = lean_ctor_get(v_a_111_, 2);
v_needlePos_160_ = lean_ctor_get(v_a_111_, 3);
v_isSharedCheck_221_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_221_ == 0)
{
v___x_162_ = v_a_111_;
v_isShared_163_ = v_isSharedCheck_221_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_needlePos_160_);
lean_inc(v_stackPos_159_);
lean_inc(v_table_158_);
lean_inc(v_needle_157_);
lean_dec(v_a_111_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_221_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_str_164_; lean_object* v_startInclusive_165_; lean_object* v_endExclusive_166_; lean_object* v_str_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v_basePos_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_str_164_ = lean_ctor_get(v_needle_157_, 0);
v_startInclusive_165_ = lean_ctor_get(v_needle_157_, 1);
v_endExclusive_166_ = lean_ctor_get(v_needle_157_, 2);
v_str_167_ = lean_ctor_get(v_s_109_, 0);
v_startInclusive_168_ = lean_ctor_get(v_s_109_, 1);
v_endExclusive_169_ = lean_ctor_get(v_s_109_, 2);
v_basePos_170_ = lean_nat_sub(v_stackPos_159_, v_needlePos_160_);
v___x_171_ = lean_nat_sub(v_endExclusive_166_, v_startInclusive_165_);
v___x_172_ = lean_nat_add(v_basePos_170_, v___x_171_);
v___x_173_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
v___x_174_ = lean_nat_dec_le(v___x_172_, v___x_173_);
lean_dec(v___x_172_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
lean_dec(v___x_171_);
lean_del_object(v___x_162_);
lean_dec(v_needlePos_160_);
lean_dec(v_stackPos_159_);
lean_dec_ref(v_table_158_);
lean_dec_ref(v_needle_157_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_basePos_170_, v___x_175_);
v___x_177_ = lean_nat_dec_le(v___x_176_, v___x_173_);
lean_dec(v___x_176_);
if (v___x_177_ == 0)
{
lean_dec(v___x_173_);
lean_dec(v_basePos_170_);
lean_dec_ref(v_s_109_);
return v_b_112_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_String_Slice_pos_x21(v_s_109_, v_basePos_170_);
lean_dec(v_basePos_170_);
v___x_179_ = lean_box(3);
v_it_114_ = v___x_179_;
v_startPos_115_ = v___x_178_;
v_endPos_116_ = v___x_173_;
goto v___jp_113_;
}
}
else
{
lean_object* v___x_180_; uint8_t v_stackByte_181_; lean_object* v___x_182_; uint8_t v_patByte_183_; uint8_t v___x_184_; 
lean_dec(v___x_173_);
v___x_180_ = lean_nat_add(v_startInclusive_168_, v_stackPos_159_);
v_stackByte_181_ = lean_string_get_byte_fast(v_str_167_, v___x_180_);
v___x_182_ = lean_nat_add(v_startInclusive_165_, v_needlePos_160_);
v_patByte_183_ = lean_string_get_byte_fast(v_str_164_, v___x_182_);
v___x_184_ = lean_uint8_dec_eq(v_stackByte_181_, v_patByte_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v_decide_186_; 
lean_dec(v___x_171_);
v___x_185_ = lean_unsigned_to_nat(0u);
v_decide_186_ = lean_nat_dec_eq(v_needlePos_160_, v___x_185_);
if (v_decide_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_newNeedlePos_189_; uint8_t v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_sub(v_needlePos_160_, v___x_187_);
lean_dec(v_needlePos_160_);
v_newNeedlePos_189_ = lean_array_fget_borrowed(v_table_158_, v___x_188_);
lean_dec(v___x_188_);
v___x_190_ = lean_nat_dec_eq(v_newNeedlePos_189_, v___x_185_);
if (v___x_190_ == 0)
{
lean_object* v_oldBasePos_191_; lean_object* v___x_192_; lean_object* v_newBasePos_193_; lean_object* v___x_195_; 
lean_inc(v_newNeedlePos_189_);
v_oldBasePos_191_ = l_String_Slice_pos_x21(v_s_109_, v_basePos_170_);
lean_dec(v_basePos_170_);
v___x_192_ = lean_nat_sub(v_stackPos_159_, v_newNeedlePos_189_);
v_newBasePos_193_ = l_String_Slice_pos_x21(v_s_109_, v___x_192_);
lean_dec(v___x_192_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v_newNeedlePos_189_);
v___x_195_ = v___x_162_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_needle_157_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_table_158_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_stackPos_159_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_newNeedlePos_189_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v_it_114_ = v___x_195_;
v_startPos_115_ = v_oldBasePos_191_;
v_endPos_116_ = v_newBasePos_193_;
goto v___jp_113_;
}
}
else
{
lean_object* v_basePos_197_; lean_object* v_nextStackPos_198_; lean_object* v___x_200_; 
v_basePos_197_ = l_String_Slice_pos_x21(v_s_109_, v_basePos_170_);
lean_dec(v_basePos_170_);
v_nextStackPos_198_ = l_String_Slice_posGE___redArg(v_s_109_, v_stackPos_159_);
lean_inc(v_nextStackPos_198_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v___x_185_);
lean_ctor_set(v___x_162_, 2, v_nextStackPos_198_);
v___x_200_ = v___x_162_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_needle_157_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_table_158_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_nextStackPos_198_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v___x_185_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v_it_114_ = v___x_200_;
v_startPos_115_ = v_basePos_197_;
v_endPos_116_ = v_nextStackPos_198_;
goto v___jp_113_;
}
}
}
else
{
lean_object* v_basePos_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_nextStackPos_205_; lean_object* v___x_207_; 
lean_dec(v_basePos_170_);
lean_dec(v_needlePos_160_);
v_basePos_202_ = l_String_Slice_pos_x21(v_s_109_, v_stackPos_159_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_stackPos_159_, v___x_203_);
lean_dec(v_stackPos_159_);
v_nextStackPos_205_ = l_String_Slice_posGE___redArg(v_s_109_, v___x_204_);
lean_inc(v_nextStackPos_205_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v___x_185_);
lean_ctor_set(v___x_162_, 2, v_nextStackPos_205_);
v___x_207_ = v___x_162_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_needle_157_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_table_158_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_nextStackPos_205_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___x_185_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v_it_114_ = v___x_207_;
v_startPos_115_ = v_basePos_202_;
v_endPos_116_ = v_nextStackPos_205_;
goto v___jp_113_;
}
}
}
else
{
lean_object* v___x_209_; lean_object* v_nextStackPos_210_; lean_object* v_nextNeedlePos_211_; uint8_t v_decide_212_; 
lean_dec(v_basePos_170_);
v___x_209_ = lean_unsigned_to_nat(1u);
v_nextStackPos_210_ = lean_nat_add(v_stackPos_159_, v___x_209_);
lean_dec(v_stackPos_159_);
v_nextNeedlePos_211_ = lean_nat_add(v_needlePos_160_, v___x_209_);
lean_dec(v_needlePos_160_);
v_decide_212_ = lean_nat_dec_eq(v_nextNeedlePos_211_, v___x_171_);
lean_dec(v___x_171_);
if (v_decide_212_ == 0)
{
lean_object* v___x_214_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v_nextNeedlePos_211_);
lean_ctor_set(v___x_162_, 2, v_nextStackPos_210_);
v___x_214_ = v___x_162_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_needle_157_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_table_158_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_nextStackPos_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_nextNeedlePos_211_);
v___x_214_ = v_reuseFailAlloc_216_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v_a_111_ = v___x_214_;
goto _start;
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v_nextNeedlePos_211_);
v___x_217_ = lean_unsigned_to_nat(0u);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v___x_217_);
lean_ctor_set(v___x_162_, 2, v_nextStackPos_210_);
v___x_219_ = v___x_162_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_needle_157_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_table_158_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_nextStackPos_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_it_125_ = v___x_219_;
goto v___jp_124_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_109_);
return v_b_112_;
}
}
v___jp_113_:
{
lean_object* v___x_117_; lean_object* v_str_118_; lean_object* v_startInclusive_119_; lean_object* v_endExclusive_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_inc_ref(v_s_109_);
v___x_117_ = l_String_Slice_slice_x21(v_s_109_, v_startPos_115_, v_endPos_116_);
lean_dec(v_endPos_116_);
lean_dec(v_startPos_115_);
v_str_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_str_118_);
v_startInclusive_119_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_startInclusive_119_);
v_endExclusive_120_ = lean_ctor_get(v___x_117_, 2);
lean_inc(v_endExclusive_120_);
lean_dec_ref(v___x_117_);
v___x_121_ = lean_string_utf8_extract_fast(v_str_118_, v_startInclusive_119_, v_endExclusive_120_);
lean_dec(v_endExclusive_120_);
lean_dec(v_startInclusive_119_);
lean_dec_ref(v_str_118_);
v___x_122_ = lean_string_append(v_b_112_, v___x_121_);
lean_dec_ref(v___x_121_);
v_a_111_ = v_it_114_;
v_b_112_ = v___x_122_;
goto _start;
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_string_utf8_byte_size(v_replacement_110_);
v___x_128_ = lean_string_utf8_extract_fast(v_replacement_110_, v___x_126_, v___x_127_);
v___x_129_ = lean_string_append(v_b_112_, v___x_128_);
lean_dec_ref(v___x_128_);
v_a_111_ = v_it_125_;
v_b_112_ = v___x_129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* v_s_222_, lean_object* v_replacement_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_222_, v_replacement_223_, v_a_224_, v_b_225_);
lean_dec_ref(v_replacement_223_);
return v_res_226_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_230_ = lean_string_utf8_byte_size(v___x_229_);
return v___x_230_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_233_ = lean_nat_dec_eq(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_234_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
v___x_237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_234_);
return v___x_237_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_239_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
v___x_242_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_243_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
lean_ctor_set(v___x_243_, 3, v___x_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* v_s_246_, lean_object* v_replacement_247_){
_start:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
v___x_249_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
v___x_251_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_246_, v_replacement_247_, v___x_250_, v___x_248_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7));
v___x_253_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_246_, v_replacement_247_, v___x_252_, v___x_248_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* v_s_254_, lean_object* v_replacement_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_254_, v_replacement_255_);
lean_dec_ref(v_replacement_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* v_leanSysroot_257_, size_t v_sz_258_, size_t v_i_259_, lean_object* v_bs_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
if (v___x_261_ == 0)
{
return v_bs_260_;
}
else
{
lean_object* v_v_262_; lean_object* v___x_263_; lean_object* v_bs_x27_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v_v_262_ = lean_array_uget(v_bs_260_, v_i_259_);
v___x_263_ = lean_unsigned_to_nat(0u);
v_bs_x27_264_ = lean_array_uset(v_bs_260_, v_i_259_, v___x_263_);
v___x_265_ = lean_string_utf8_byte_size(v_v_262_);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v_v_262_);
lean_ctor_set(v___x_266_, 1, v___x_263_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
v___x_267_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_266_, v_leanSysroot_257_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_259_, v___x_268_);
v___x_270_ = lean_array_uset(v_bs_x27_264_, v_i_259_, v___x_267_);
v_i_259_ = v___x_269_;
v_bs_260_ = v___x_270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* v_leanSysroot_272_, lean_object* v_sz_273_, lean_object* v_i_274_, lean_object* v_bs_275_){
_start:
{
size_t v_sz_boxed_276_; size_t v_i_boxed_277_; lean_object* v_res_278_; 
v_sz_boxed_276_ = lean_unbox_usize(v_sz_273_);
lean_dec(v_sz_273_);
v_i_boxed_277_ = lean_unbox_usize(v_i_274_);
lean_dec(v_i_274_);
v_res_278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_272_, v_sz_boxed_276_, v_i_boxed_277_, v_bs_275_);
lean_dec_ref(v_leanSysroot_272_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(0);
v___x_280_ = lean_get_leanc_internal_flags(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__0, &l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
v___x_282_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_281_);
return v___x_282_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2(void){
_start:
{
lean_object* v___x_283_; size_t v_sz_284_; 
v___x_283_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_284_ = lean_array_size(v___x_283_);
return v_sz_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* v_leanSysroot_285_){
_start:
{
lean_object* v___x_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_286_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_287_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__2, &l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
v___x_288_ = ((size_t)0ULL);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_285_, v_sz_287_, v___x_288_, v___x_286_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* v_leanSysroot_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_290_);
lean_dec_ref(v_leanSysroot_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* v_s_292_, lean_object* v_pattern_293_, lean_object* v_replacement_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_292_, v_replacement_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* v_s_296_, lean_object* v_pattern_297_, lean_object* v_replacement_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(v_s_296_, v_pattern_297_, v_replacement_298_);
lean_dec_ref(v_replacement_298_);
lean_dec_ref(v_pattern_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* v_s_300_, lean_object* v_replacement_301_, lean_object* v_inst_302_, lean_object* v_R_303_, lean_object* v_a_304_, lean_object* v_b_305_, lean_object* v_c_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_300_, v_replacement_301_, v_a_304_, v_b_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* v_s_308_, lean_object* v_replacement_309_, lean_object* v_inst_310_, lean_object* v_R_311_, lean_object* v_a_312_, lean_object* v_b_313_, lean_object* v_c_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_308_, v_replacement_309_, v_inst_310_, v_R_311_, v_a_312_, v_b_313_, v_c_314_);
lean_dec_ref(v_replacement_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* v_linkStatic_317_){
_start:
{
uint8_t v_linkStatic_boxed_318_; lean_object* v_res_319_; 
v_linkStatic_boxed_318_ = lean_unbox(v_linkStatic_317_);
v_res_319_ = lean_get_linker_flags(v_linkStatic_boxed_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t v_linkStatic_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_get_linker_flags(v_linkStatic_320_);
v___x_322_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* v_linkStatic_323_){
_start:
{
uint8_t v_linkStatic_boxed_324_; lean_object* v_res_325_; 
v_linkStatic_boxed_324_ = lean_unbox(v_linkStatic_323_);
v_res_325_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_boxed_324_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__0));
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_array_push(v___x_331_, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* v_leanSysroot_333_, uint8_t v_linkStatic_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_335_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__1));
v___x_336_ = l_System_FilePath_join(v_leanSysroot_333_, v___x_335_);
v___x_337_ = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__2));
v___x_338_ = l_System_FilePath_join(v___x_336_, v___x_337_);
v___x_339_ = lean_obj_once(&l_Lean_Compiler_FFI_getLinkerFlags___closed__3, &l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once, _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
v___x_340_ = lean_array_push(v___x_339_, v___x_338_);
v___x_341_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_334_);
v___x_342_ = l_Array_append___redArg(v___x_340_, v___x_341_);
lean_dec_ref(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* v_leanSysroot_343_, lean_object* v_linkStatic_344_){
_start:
{
uint8_t v_linkStatic_boxed_345_; lean_object* v_res_346_; 
v_linkStatic_boxed_345_ = lean_unbox(v_linkStatic_344_);
v_res_346_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_343_, v_linkStatic_boxed_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* v_a_00___x40___internal___hyg_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_348_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
v___x_351_ = lean_get_internal_linker_flags(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
v___x_353_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_352_);
return v___x_353_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2(void){
_start:
{
lean_object* v___x_354_; size_t v_sz_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_355_ = lean_array_size(v___x_354_);
return v_sz_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* v_leanSysroot_356_){
_start:
{
lean_object* v___x_357_; size_t v_sz_358_; size_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_358_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_356_, v_sz_358_, v___x_359_, v___x_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* v_leanSysroot_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_361_);
lean_dec_ref(v_leanSysroot_361_);
return v_res_362_;
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
