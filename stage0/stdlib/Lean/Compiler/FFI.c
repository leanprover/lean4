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
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4;
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
LEAN_EXPORT void l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_get_leanc_extra_flags(v_a_00___x40___internal___hyg_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_get_leanc_extra_flags(v_a_00___x40___internal___hyg_3_);
return v_res_4_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg(){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___closed__0));
return v___x_8_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_9_;
v_res_9_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg___boxed(lean_object* v___dummy_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
return v_res_11_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___redArg();
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* v_s_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* v_s_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v_s_15_);
lean_dec_ref(v_s_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object* v_s_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v_it_23_; lean_object* v_startInclusive_24_; lean_object* v_endExclusive_25_; 
if (lean_obj_tag(v_a_20_) == 0)
{
lean_object* v_currPos_34_; lean_object* v_searcher_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_58_; 
v_currPos_34_ = lean_ctor_get(v_a_20_, 0);
v_searcher_35_ = lean_ctor_get(v_a_20_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v_a_20_);
if (v_isSharedCheck_58_ == 0)
{
v___x_37_ = v_a_20_;
v_isShared_38_ = v_isSharedCheck_58_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_searcher_35_);
lean_inc(v_currPos_34_);
lean_dec(v_a_20_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_58_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v_decide_39_; 
v_decide_39_ = lean_nat_dec_eq(v_searcher_35_, v___x_19_);
if (v_decide_39_ == 0)
{
uint32_t v___x_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = 32;
v___x_41_ = lean_string_utf8_get_fast(v_s_17_, v_searcher_35_);
v___x_42_ = lean_uint32_dec_eq(v___x_41_, v___x_40_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = lean_string_utf8_next_fast(v_s_17_, v_searcher_35_);
lean_dec(v_searcher_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_43_);
v___x_45_ = v___x_37_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_currPos_34_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_47_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
v_a_20_ = v___x_45_;
goto _start;
}
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v_slice_51_; lean_object* v_nextIt_53_; 
v___x_48_ = lean_string_utf8_next_fast(v_s_17_, v_searcher_35_);
v___x_49_ = lean_nat_sub(v___x_48_, v_searcher_35_);
v___x_50_ = lean_nat_add(v_searcher_35_, v___x_49_);
lean_dec(v___x_49_);
v_slice_51_ = l_String_Slice_subslice_x21(v___x_18_, v_currPos_34_, v_searcher_35_);
lean_inc(v___x_50_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_50_);
lean_ctor_set(v___x_37_, 0, v___x_50_);
v_nextIt_53_ = v___x_37_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_50_);
v_nextIt_53_ = v_reuseFailAlloc_56_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; 
v_startInclusive_54_ = lean_ctor_get(v_slice_51_, 0);
lean_inc(v_startInclusive_54_);
v_endExclusive_55_ = lean_ctor_get(v_slice_51_, 1);
lean_inc(v_endExclusive_55_);
lean_dec_ref(v_slice_51_);
v_it_23_ = v_nextIt_53_;
v_startInclusive_24_ = v_startInclusive_54_;
v_endExclusive_25_ = v_endExclusive_55_;
goto v___jp_22_;
}
}
}
else
{
lean_object* v___x_57_; 
lean_del_object(v___x_37_);
lean_dec(v_searcher_35_);
v___x_57_ = lean_box(1);
lean_inc(v___x_19_);
v_it_23_ = v___x_57_;
v_startInclusive_24_ = v_currPos_34_;
v_endExclusive_25_ = v___x_19_;
goto v___jp_22_;
}
}
}
else
{
lean_dec(v___x_19_);
lean_dec_ref(v_s_17_);
return v_b_21_;
}
v___jp_22_:
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_nat_sub(v_endExclusive_25_, v_startInclusive_24_);
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_inc_ref(v_s_17_);
v___x_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_29_, 0, v_s_17_);
lean_ctor_set(v___x_29_, 1, v_startInclusive_24_);
lean_ctor_set(v___x_29_, 2, v_endExclusive_25_);
v___x_30_ = l_String_Slice_toString(v___x_29_);
lean_dec_ref_known(v___x_29_, 3);
v___x_31_ = lean_array_push(v_b_21_, v___x_30_);
v_a_20_ = v_it_23_;
v_b_21_ = v___x_31_;
goto _start;
}
else
{
lean_dec(v_endExclusive_25_);
lean_dec(v_startInclusive_24_);
v_a_20_ = v_it_23_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* v_s_59_, lean_object* v___x_60_, lean_object* v___x_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_59_, v___x_60_, v___x_61_, v_a_62_, v_b_63_);
lean_dec_ref(v___x_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_string_utf8_byte_size(v_s_67_);
lean_inc_ref(v_s_67_);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_s_67_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_69_);
v___x_71_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
v___x_72_ = ((lean_object*)(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0));
v___x_73_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_67_, v___x_70_, v___x_69_, v___x_71_, v___x_72_);
lean_dec_ref_known(v___x_70_, 3);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* v_s_74_, lean_object* v___x_75_, lean_object* v___x_76_, lean_object* v_inst_77_, lean_object* v_R_78_, lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_74_, v___x_75_, v___x_76_, v_a_79_, v_b_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* v_s_82_, lean_object* v___x_83_, lean_object* v___x_84_, lean_object* v_inst_85_, lean_object* v_R_86_, lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_82_, v___x_83_, v___x_84_, v_inst_85_, v_R_86_, v_a_87_, v_b_88_);
lean_dec_ref(v___x_83_);
return v_res_89_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_get_leanc_extra_flags(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__0, &l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
v___x_93_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags_x27___closed__1, &l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once, _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_array_push(v___x_99_, v___x_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* v_leanSysroot_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_102_ = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
v___x_103_ = l_System_FilePath_join(v_leanSysroot_101_, v___x_102_);
v___x_104_ = lean_obj_once(&l_Lean_Compiler_FFI_getCFlags___closed__2, &l_Lean_Compiler_FFI_getCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getCFlags___closed__2);
v___x_105_ = lean_array_push(v___x_104_, v___x_103_);
v___x_106_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_107_ = l_Array_append___redArg(v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_108_ = stack[0].m_obj;
lean_object* v_res_109_;
v_res_109_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_108_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* v_a_00___x40___internal___hyg_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* v_s_112_, lean_object* v_replacement_113_, lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_it_117_; lean_object* v_startPos_118_; lean_object* v_endPos_119_; lean_object* v_it_128_; 
switch(lean_obj_tag(v_a_114_))
{
case 0:
{
lean_object* v_pos_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_146_; 
v_pos_134_ = lean_ctor_get(v_a_114_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_146_ == 0)
{
v___x_136_ = v_a_114_;
v_isShared_137_ = v_isSharedCheck_146_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_pos_134_);
lean_dec(v_a_114_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_146_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_startInclusive_138_; lean_object* v_endExclusive_139_; lean_object* v___x_140_; uint8_t v_decide_141_; 
v_startInclusive_138_ = lean_ctor_get(v_s_112_, 1);
v_endExclusive_139_ = lean_ctor_get(v_s_112_, 2);
v___x_140_ = lean_nat_sub(v_endExclusive_139_, v_startInclusive_138_);
v_decide_141_ = lean_nat_dec_eq(v_pos_134_, v___x_140_);
lean_dec(v___x_140_);
if (v_decide_141_ == 0)
{
lean_object* v___x_143_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 1);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_pos_134_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_it_128_ = v___x_143_;
goto v___jp_127_;
}
}
else
{
lean_object* v___x_145_; 
lean_del_object(v___x_136_);
lean_dec(v_pos_134_);
v___x_145_ = lean_box(3);
v_it_128_ = v___x_145_;
goto v___jp_127_;
}
}
}
case 1:
{
lean_object* v_pos_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_159_; 
v_pos_147_ = lean_ctor_get(v_a_114_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_159_ == 0)
{
v___x_149_ = v_a_114_;
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_pos_147_);
lean_dec(v_a_114_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_str_151_; lean_object* v_startInclusive_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v_str_151_ = lean_ctor_get(v_s_112_, 0);
v_startInclusive_152_ = lean_ctor_get(v_s_112_, 1);
v___x_153_ = lean_nat_add(v_startInclusive_152_, v_pos_147_);
v___x_154_ = lean_string_utf8_next_fast(v_str_151_, v___x_153_);
lean_dec(v___x_153_);
v___x_155_ = lean_nat_sub(v___x_154_, v_startInclusive_152_);
lean_inc(v___x_155_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 0);
lean_ctor_set(v___x_149_, 0, v___x_155_);
v___x_157_ = v___x_149_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v_it_117_ = v___x_157_;
v_startPos_118_ = v_pos_147_;
v_endPos_119_ = v___x_155_;
goto v___jp_116_;
}
}
}
case 2:
{
lean_object* v_needle_160_; lean_object* v_table_161_; lean_object* v_stackPos_162_; lean_object* v_needlePos_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_224_; 
v_needle_160_ = lean_ctor_get(v_a_114_, 0);
v_table_161_ = lean_ctor_get(v_a_114_, 1);
v_stackPos_162_ = lean_ctor_get(v_a_114_, 2);
v_needlePos_163_ = lean_ctor_get(v_a_114_, 3);
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_224_ == 0)
{
v___x_165_ = v_a_114_;
v_isShared_166_ = v_isSharedCheck_224_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_needlePos_163_);
lean_inc(v_stackPos_162_);
lean_inc(v_table_161_);
lean_inc(v_needle_160_);
lean_dec(v_a_114_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_224_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_str_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v_str_170_; lean_object* v_startInclusive_171_; lean_object* v_endExclusive_172_; lean_object* v_basePos_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_str_167_ = lean_ctor_get(v_needle_160_, 0);
v_startInclusive_168_ = lean_ctor_get(v_needle_160_, 1);
v_endExclusive_169_ = lean_ctor_get(v_needle_160_, 2);
v_str_170_ = lean_ctor_get(v_s_112_, 0);
v_startInclusive_171_ = lean_ctor_get(v_s_112_, 1);
v_endExclusive_172_ = lean_ctor_get(v_s_112_, 2);
v_basePos_173_ = lean_nat_sub(v_stackPos_162_, v_needlePos_163_);
v___x_174_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
v___x_175_ = lean_nat_add(v_basePos_173_, v___x_174_);
v___x_176_ = lean_nat_sub(v_endExclusive_172_, v_startInclusive_171_);
v___x_177_ = lean_nat_dec_le(v___x_175_, v___x_176_);
lean_dec(v___x_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
lean_dec(v___x_174_);
lean_del_object(v___x_165_);
lean_dec(v_needlePos_163_);
lean_dec(v_stackPos_162_);
lean_dec_ref(v_table_161_);
lean_dec_ref(v_needle_160_);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_basePos_173_, v___x_178_);
v___x_180_ = lean_nat_dec_le(v___x_179_, v___x_176_);
lean_dec(v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v___x_176_);
lean_dec(v_basePos_173_);
lean_dec_ref(v_s_112_);
return v_b_115_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = l_String_Slice_pos_x21(v_s_112_, v_basePos_173_);
lean_dec(v_basePos_173_);
v___x_182_ = lean_box(3);
v_it_117_ = v___x_182_;
v_startPos_118_ = v___x_181_;
v_endPos_119_ = v___x_176_;
goto v___jp_116_;
}
}
else
{
lean_object* v___x_183_; uint8_t v_stackByte_184_; lean_object* v___x_185_; uint8_t v_patByte_186_; uint8_t v___x_187_; 
lean_dec(v___x_176_);
v___x_183_ = lean_nat_add(v_startInclusive_171_, v_stackPos_162_);
v_stackByte_184_ = lean_string_get_byte_fast(v_str_170_, v___x_183_);
v___x_185_ = lean_nat_add(v_startInclusive_168_, v_needlePos_163_);
v_patByte_186_ = lean_string_get_byte_fast(v_str_167_, v___x_185_);
v___x_187_ = lean_uint8_dec_eq(v_stackByte_184_, v_patByte_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; uint8_t v_decide_189_; 
lean_dec(v___x_174_);
v___x_188_ = lean_unsigned_to_nat(0u);
v_decide_189_ = lean_nat_dec_eq(v_needlePos_163_, v___x_188_);
if (v_decide_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_newNeedlePos_192_; uint8_t v___x_193_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_sub(v_needlePos_163_, v___x_190_);
lean_dec(v_needlePos_163_);
v_newNeedlePos_192_ = lean_array_fget_borrowed(v_table_161_, v___x_191_);
lean_dec(v___x_191_);
v___x_193_ = lean_nat_dec_eq(v_newNeedlePos_192_, v___x_188_);
if (v___x_193_ == 0)
{
lean_object* v_oldBasePos_194_; lean_object* v___x_195_; lean_object* v_newBasePos_196_; lean_object* v___x_198_; 
lean_inc(v_newNeedlePos_192_);
v_oldBasePos_194_ = l_String_Slice_pos_x21(v_s_112_, v_basePos_173_);
lean_dec(v_basePos_173_);
v___x_195_ = lean_nat_sub(v_stackPos_162_, v_newNeedlePos_192_);
v_newBasePos_196_ = l_String_Slice_pos_x21(v_s_112_, v___x_195_);
lean_dec(v___x_195_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v_newNeedlePos_192_);
v___x_198_ = v___x_165_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_needle_160_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_table_161_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_stackPos_162_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_newNeedlePos_192_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_it_117_ = v___x_198_;
v_startPos_118_ = v_oldBasePos_194_;
v_endPos_119_ = v_newBasePos_196_;
goto v___jp_116_;
}
}
else
{
lean_object* v_basePos_200_; lean_object* v_nextStackPos_201_; lean_object* v___x_203_; 
v_basePos_200_ = l_String_Slice_pos_x21(v_s_112_, v_basePos_173_);
lean_dec(v_basePos_173_);
v_nextStackPos_201_ = l_String_Slice_posGE___redArg(v_s_112_, v_stackPos_162_);
lean_inc(v_nextStackPos_201_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v___x_188_);
lean_ctor_set(v___x_165_, 2, v_nextStackPos_201_);
v___x_203_ = v___x_165_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_needle_160_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_table_161_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_nextStackPos_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___x_188_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_it_117_ = v___x_203_;
v_startPos_118_ = v_basePos_200_;
v_endPos_119_ = v_nextStackPos_201_;
goto v___jp_116_;
}
}
}
else
{
lean_object* v_basePos_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_nextStackPos_208_; lean_object* v___x_210_; 
lean_dec(v_basePos_173_);
lean_dec(v_needlePos_163_);
v_basePos_205_ = l_String_Slice_pos_x21(v_s_112_, v_stackPos_162_);
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_stackPos_162_, v___x_206_);
lean_dec(v_stackPos_162_);
v_nextStackPos_208_ = l_String_Slice_posGE___redArg(v_s_112_, v___x_207_);
lean_inc(v_nextStackPos_208_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v___x_188_);
lean_ctor_set(v___x_165_, 2, v_nextStackPos_208_);
v___x_210_ = v___x_165_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_needle_160_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_table_161_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_nextStackPos_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v___x_188_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_it_117_ = v___x_210_;
v_startPos_118_ = v_basePos_205_;
v_endPos_119_ = v_nextStackPos_208_;
goto v___jp_116_;
}
}
}
else
{
lean_object* v___x_212_; lean_object* v_nextStackPos_213_; lean_object* v_nextNeedlePos_214_; uint8_t v_decide_215_; 
lean_dec(v_basePos_173_);
v___x_212_ = lean_unsigned_to_nat(1u);
v_nextStackPos_213_ = lean_nat_add(v_stackPos_162_, v___x_212_);
lean_dec(v_stackPos_162_);
v_nextNeedlePos_214_ = lean_nat_add(v_needlePos_163_, v___x_212_);
lean_dec(v_needlePos_163_);
v_decide_215_ = lean_nat_dec_eq(v_nextNeedlePos_214_, v___x_174_);
lean_dec(v___x_174_);
if (v_decide_215_ == 0)
{
lean_object* v___x_217_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v_nextNeedlePos_214_);
lean_ctor_set(v___x_165_, 2, v_nextStackPos_213_);
v___x_217_ = v___x_165_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_needle_160_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_table_161_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_nextStackPos_213_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_nextNeedlePos_214_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
v_a_114_ = v___x_217_;
goto _start;
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_nextNeedlePos_214_);
v___x_220_ = lean_unsigned_to_nat(0u);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 3, v___x_220_);
lean_ctor_set(v___x_165_, 2, v_nextStackPos_213_);
v___x_222_ = v___x_165_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_needle_160_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_table_161_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_nextStackPos_213_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v_it_128_ = v___x_222_;
goto v___jp_127_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_112_);
return v_b_115_;
}
}
v___jp_116_:
{
lean_object* v___x_120_; lean_object* v_str_121_; lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc_ref(v_s_112_);
v___x_120_ = l_String_Slice_slice_x21(v_s_112_, v_startPos_118_, v_endPos_119_);
lean_dec(v_endPos_119_);
lean_dec(v_startPos_118_);
v_str_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc_ref(v_str_121_);
v_startInclusive_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_startInclusive_122_);
v_endExclusive_123_ = lean_ctor_get(v___x_120_, 2);
lean_inc(v_endExclusive_123_);
lean_dec_ref(v___x_120_);
v___x_124_ = lean_string_utf8_extract_fast(v_str_121_, v_startInclusive_122_, v_endExclusive_123_);
lean_dec(v_endExclusive_123_);
lean_dec(v_startInclusive_122_);
lean_dec_ref(v_str_121_);
v___x_125_ = lean_string_append(v_b_115_, v___x_124_);
lean_dec_ref(v___x_124_);
v_a_114_ = v_it_117_;
v_b_115_ = v___x_125_;
goto _start;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_string_utf8_byte_size(v_replacement_113_);
v___x_131_ = lean_string_utf8_extract_fast(v_replacement_113_, v___x_129_, v___x_130_);
v___x_132_ = lean_string_append(v_b_115_, v___x_131_);
lean_dec_ref(v___x_131_);
v_a_114_ = v_it_128_;
v_b_115_ = v___x_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* v_s_225_, lean_object* v_replacement_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_225_, v_replacement_226_, v_a_227_, v_b_228_);
lean_dec_ref(v_replacement_226_);
return v_res_229_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2));
v___x_237_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
v___x_240_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2));
v___x_241_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_238_);
lean_ctor_set(v___x_241_, 3, v___x_238_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* v_s_242_, lean_object* v_replacement_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
v___x_245_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_242_, v_replacement_243_, v___x_245_, v___x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* v_s_247_, lean_object* v_replacement_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_247_, v_replacement_248_);
lean_dec_ref(v_replacement_248_);
return v_res_249_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* v_leanSysroot_250_, size_t v_sz_251_, size_t v_i_252_, lean_object* v_bs_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_usize_dec_lt(v_i_252_, v_sz_251_);
if (v___x_254_ == 0)
{
return v_bs_253_;
}
else
{
lean_object* v_v_255_; lean_object* v___x_256_; lean_object* v_bs_x27_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; 
v_v_255_ = lean_array_uget(v_bs_253_, v_i_252_);
v___x_256_ = lean_unsigned_to_nat(0u);
v_bs_x27_257_ = lean_array_uset(v_bs_253_, v_i_252_, v___x_256_);
v___x_258_ = lean_string_utf8_byte_size(v_v_255_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v_v_255_);
lean_ctor_set(v___x_259_, 1, v___x_256_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
v___x_260_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_259_, v_leanSysroot_250_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_252_, v___x_261_);
v___x_263_ = lean_array_uset(v_bs_x27_257_, v_i_252_, v___x_260_);
v_i_252_ = v___x_262_;
v_bs_253_ = v___x_263_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanSysroot_250_ = stack[0].m_obj;
size_t v_sz_251_ = stack[1].m_num;
size_t v_i_252_ = stack[2].m_num;
lean_object* v_bs_253_ = stack[3].m_obj;
lean_object* v_res_265_;
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_250_, v_sz_251_, v_i_252_, v_bs_253_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* v_leanSysroot_266_, lean_object* v_sz_267_, lean_object* v_i_268_, lean_object* v_bs_269_){
_start:
{
size_t v_sz_boxed_270_; size_t v_i_boxed_271_; lean_object* v_res_272_; 
v_sz_boxed_270_ = lean_unbox_usize(v_sz_267_);
lean_dec(v_sz_267_);
v_i_boxed_271_ = lean_unbox_usize(v_i_268_);
lean_dec(v_i_268_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_266_, v_sz_boxed_270_, v_i_boxed_271_, v_bs_269_);
lean_dec_ref(v_leanSysroot_266_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_get_leanc_internal_flags(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__0, &l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
v___x_276_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_275_);
return v___x_276_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2(void){
_start:
{
lean_object* v___x_277_; size_t v_sz_278_; 
v___x_277_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_278_ = lean_array_size(v___x_277_);
return v_sz_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* v_leanSysroot_279_){
_start:
{
lean_object* v___x_280_; size_t v_sz_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__1, &l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
v_sz_281_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalCFlags___closed__2, &l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
v___x_282_ = ((size_t)0ULL);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_279_, v_sz_281_, v___x_282_, v___x_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* v_leanSysroot_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_284_);
lean_dec_ref(v_leanSysroot_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* v_s_286_, lean_object* v_pattern_287_, lean_object* v_replacement_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v_s_286_, v_replacement_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* v_s_290_, lean_object* v_pattern_291_, lean_object* v_replacement_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(v_s_290_, v_pattern_291_, v_replacement_292_);
lean_dec_ref(v_replacement_292_);
lean_dec_ref(v_pattern_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* v_s_294_, lean_object* v_replacement_295_, lean_object* v_inst_296_, lean_object* v_R_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v_c_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_294_, v_replacement_295_, v_a_298_, v_b_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* v_s_302_, lean_object* v_replacement_303_, lean_object* v_inst_304_, lean_object* v_R_305_, lean_object* v_a_306_, lean_object* v_b_307_, lean_object* v_c_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_302_, v_replacement_303_, v_inst_304_, v_R_305_, v_a_306_, v_b_307_, v_c_308_);
lean_dec_ref(v_replacement_303_);
return v_res_309_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags_0interp(lean_interpreter_value* stack)
{
uint8_t v_linkStatic_310_ = stack[0].m_num;
lean_object* v_res_311_;
v_res_311_ = lean_get_linker_flags(v_linkStatic_310_);
stack->m_obj
 = v_res_311_;
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
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t v_linkStatic_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_get_linker_flags(v_linkStatic_315_);
v___x_317_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Lean_Compiler_FFI_getLinkerFlags_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_linkStatic_315_ = stack[0].m_num;
lean_object* v_res_318_;
v_res_318_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_315_);
stack->m_obj
 = v_res_318_;
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
lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* v_leanSysroot_329_, uint8_t v_linkStatic_330_){
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
LEAN_EXPORT void l_Lean_Compiler_FFI_getLinkerFlags_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanSysroot_329_ = stack[0].m_obj;
uint8_t v_linkStatic_330_ = stack[1].m_num;
lean_object* v_res_339_;
v_res_339_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_329_, v_linkStatic_330_);
stack->m_obj
 = v_res_339_;
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
LEAN_EXPORT void l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_344_ = stack[0].m_obj;
lean_object* v_res_345_;
v_res_345_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_344_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* v_a_00___x40___internal___hyg_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_346_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_get_internal_linker_flags(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
v___x_351_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_350_);
return v___x_351_;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2(void){
_start:
{
lean_object* v___x_352_; size_t v_sz_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_353_ = lean_array_size(v___x_352_);
return v_sz_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* v_leanSysroot_354_){
_start:
{
lean_object* v___x_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
v_sz_356_ = lean_usize_once(&l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2, &l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once, _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
v___x_357_ = ((size_t)0ULL);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_354_, v_sz_356_, v___x_357_, v___x_355_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* v_leanSysroot_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_359_);
lean_dec_ref(v_leanSysroot_359_);
return v_res_360_;
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
