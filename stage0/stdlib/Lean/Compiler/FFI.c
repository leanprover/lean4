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
lean_object* lean_get_leanc_extra_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
static const lean_string_object l_Lean_Compiler_FFI_getCFlags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lean_Compiler_FFI_getCFlags___closed__0 = (const lean_object*)&l_Lean_Compiler_FFI_getCFlags___closed__0_value;
static const lean_string_object l_Lean_Compiler_FFI_getCFlags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1 = (const lean_object*)&l_Lean_Compiler_FFI_getCFlags___closed__1_value;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
lean_object* lean_get_leanc_internal_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ROOT"};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value;
static const lean_string_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2;
static uint8_t l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5;
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6;
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
size_t lean_array_size(lean_object*);
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
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_nat_sub(x_22, x_21);
x_24 = lean_nat_dec_eq(x_20, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint32_t x_25; uint32_t x_26; uint8_t x_27; 
x_25 = 32;
x_26 = lean_string_utf8_get_fast(x_1, x_20);
x_27 = lean_uint32_dec_eq(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_string_utf8_next_fast(x_1, x_20);
lean_dec(x_20);
lean_ctor_set(x_4, 1, x_28);
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_string_utf8_next_fast(x_1, x_20);
x_31 = lean_nat_sub(x_30, x_20);
x_32 = lean_nat_add(x_20, x_31);
lean_dec(x_31);
x_33 = l_String_Slice_subslice_x21(x_2, x_19, x_20);
lean_inc(x_32);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_6 = x_4;
x_7 = x_34;
x_8 = x_35;
goto block_17;
}
}
else
{
lean_object* x_36; 
lean_free_object(x_4);
lean_dec(x_20);
x_36 = lean_box(1);
lean_inc(x_3);
x_6 = x_36;
x_7 = x_19;
x_8 = x_3;
goto block_17;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
x_41 = lean_nat_sub(x_40, x_39);
x_42 = lean_nat_dec_eq(x_38, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_43 = 32;
x_44 = lean_string_utf8_get_fast(x_1, x_38);
x_45 = lean_uint32_dec_eq(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_string_utf8_next_fast(x_1, x_38);
lean_dec(x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_string_utf8_next_fast(x_1, x_38);
x_50 = lean_nat_sub(x_49, x_38);
x_51 = lean_nat_add(x_38, x_50);
lean_dec(x_50);
x_52 = l_String_Slice_subslice_x21(x_2, x_37, x_38);
lean_inc(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec_ref(x_52);
x_6 = x_53;
x_7 = x_54;
x_8 = x_55;
goto block_17;
}
}
else
{
lean_object* x_56; 
lean_dec(x_38);
x_56 = lean_box(1);
lean_inc(x_3);
x_6 = x_56;
x_7 = x_37;
x_8 = x_3;
goto block_17;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
block_17:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_nat_sub(x_8, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
x_13 = l_String_Slice_toString(x_12);
lean_dec_ref(x_12);
x_14 = lean_array_push(x_5, x_13);
x_4 = x_6;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_4);
x_6 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(x_1, x_4, x_3, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__0));
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = ((lean_object*)(l_Lean_Compiler_FFI_getCFlags___closed__1));
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_Compiler_FFI_getCFlags_x27;
x_7 = l_Array_append___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_internal_flags(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_16; 
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_nat_sub(x_26, x_25);
x_28 = lean_nat_dec_eq(x_24, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_ctor_set_tag(x_3, 1);
x_16 = x_3;
goto block_22;
}
else
{
lean_object* x_29; 
lean_free_object(x_3);
lean_dec(x_24);
x_29 = lean_box(3);
x_16 = x_29;
goto block_22;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_nat_sub(x_32, x_31);
x_34 = lean_nat_dec_eq(x_30, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_16 = x_35;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_30);
x_36 = lean_box(3);
x_16 = x_36;
goto block_22;
}
}
}
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_nat_add(x_40, x_38);
x_42 = lean_string_utf8_next_fast(x_39, x_41);
lean_dec(x_41);
x_43 = lean_nat_sub(x_42, x_40);
lean_inc(x_43);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_43);
x_5 = x_3;
x_6 = x_38;
x_7 = x_43;
goto block_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_nat_add(x_46, x_44);
x_48 = lean_string_utf8_next_fast(x_45, x_47);
lean_dec(x_47);
x_49 = lean_nat_sub(x_48, x_46);
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_5 = x_50;
x_6 = x_44;
x_7 = x_49;
goto block_15;
}
}
case 2:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_3);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_nat_sub(x_58, x_57);
x_60 = lean_nat_dec_lt(x_54, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
lean_free_object(x_3);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_55);
if (x_62 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_nat_sub(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
x_64 = l_String_Slice_pos_x21(x_1, x_63);
lean_dec(x_63);
x_65 = lean_box(3);
x_5 = x_65;
x_6 = x_64;
x_7 = x_59;
goto block_15;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; 
lean_dec(x_59);
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
x_68 = lean_ctor_get(x_52, 2);
x_69 = lean_nat_add(x_57, x_54);
x_70 = lean_string_get_byte_fast(x_56, x_69);
x_71 = lean_nat_add(x_67, x_55);
x_72 = lean_string_get_byte_fast(x_66, x_71);
x_73 = lean_uint8_dec_eq(x_70, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_55, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_55, x_76);
x_78 = lean_array_fget_borrowed(x_53, x_77);
lean_dec(x_77);
x_79 = lean_nat_dec_eq(x_78, x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_78);
x_80 = lean_nat_sub(x_54, x_55);
lean_dec(x_55);
x_81 = l_String_Slice_pos_x21(x_1, x_80);
lean_dec(x_80);
x_82 = lean_nat_sub(x_54, x_78);
x_83 = l_String_Slice_pos_x21(x_1, x_82);
lean_dec(x_82);
lean_ctor_set(x_3, 3, x_78);
x_5 = x_3;
x_6 = x_81;
x_7 = x_83;
goto block_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_nat_sub(x_54, x_55);
lean_dec(x_55);
x_85 = l_String_Slice_pos_x21(x_1, x_84);
lean_dec(x_84);
x_86 = l_String_Slice_posGE___redArg(x_1, x_54);
lean_inc(x_86);
lean_ctor_set(x_3, 3, x_74);
lean_ctor_set(x_3, 2, x_86);
x_5 = x_3;
x_6 = x_85;
x_7 = x_86;
goto block_15;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_55);
x_87 = l_String_Slice_pos_x21(x_1, x_54);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_54, x_88);
lean_dec(x_54);
x_90 = l_String_Slice_posGE___redArg(x_1, x_89);
lean_inc(x_90);
lean_ctor_set(x_3, 3, x_74);
lean_ctor_set(x_3, 2, x_90);
x_5 = x_3;
x_6 = x_87;
x_7 = x_90;
goto block_15;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_54, x_91);
lean_dec(x_54);
x_93 = lean_nat_add(x_55, x_91);
lean_dec(x_55);
x_94 = lean_nat_sub(x_68, x_67);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_ctor_set(x_3, 3, x_93);
lean_ctor_set(x_3, 2, x_92);
goto _start;
}
else
{
lean_object* x_97; 
lean_dec(x_93);
x_97 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_3, 3, x_97);
lean_ctor_set(x_3, 2, x_92);
x_16 = x_3;
goto block_22;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_98 = lean_ctor_get(x_3, 0);
x_99 = lean_ctor_get(x_3, 1);
x_100 = lean_ctor_get(x_3, 2);
x_101 = lean_ctor_get(x_3, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_3);
x_102 = lean_ctor_get(x_1, 0);
x_103 = lean_ctor_get(x_1, 1);
x_104 = lean_ctor_get(x_1, 2);
x_105 = lean_nat_sub(x_104, x_103);
x_106 = lean_nat_dec_lt(x_100, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_lt(x_107, x_101);
if (x_108 == 0)
{
lean_dec(x_105);
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_nat_sub(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
x_110 = l_String_Slice_pos_x21(x_1, x_109);
lean_dec(x_109);
x_111 = lean_box(3);
x_5 = x_111;
x_6 = x_110;
x_7 = x_105;
goto block_15;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
lean_dec(x_105);
x_112 = lean_ctor_get(x_98, 0);
x_113 = lean_ctor_get(x_98, 1);
x_114 = lean_ctor_get(x_98, 2);
x_115 = lean_nat_add(x_103, x_100);
x_116 = lean_string_get_byte_fast(x_102, x_115);
x_117 = lean_nat_add(x_113, x_101);
x_118 = lean_string_get_byte_fast(x_112, x_117);
x_119 = lean_uint8_dec_eq(x_116, x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_dec_eq(x_101, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_sub(x_101, x_122);
x_124 = lean_array_fget_borrowed(x_99, x_123);
lean_dec(x_123);
x_125 = lean_nat_dec_eq(x_124, x_120);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc(x_124);
x_126 = lean_nat_sub(x_100, x_101);
lean_dec(x_101);
x_127 = l_String_Slice_pos_x21(x_1, x_126);
lean_dec(x_126);
x_128 = lean_nat_sub(x_100, x_124);
x_129 = l_String_Slice_pos_x21(x_1, x_128);
lean_dec(x_128);
x_130 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_130, 0, x_98);
lean_ctor_set(x_130, 1, x_99);
lean_ctor_set(x_130, 2, x_100);
lean_ctor_set(x_130, 3, x_124);
x_5 = x_130;
x_6 = x_127;
x_7 = x_129;
goto block_15;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_nat_sub(x_100, x_101);
lean_dec(x_101);
x_132 = l_String_Slice_pos_x21(x_1, x_131);
lean_dec(x_131);
x_133 = l_String_Slice_posGE___redArg(x_1, x_100);
lean_inc(x_133);
x_134 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_134, 0, x_98);
lean_ctor_set(x_134, 1, x_99);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_120);
x_5 = x_134;
x_6 = x_132;
x_7 = x_133;
goto block_15;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_101);
x_135 = l_String_Slice_pos_x21(x_1, x_100);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_100, x_136);
lean_dec(x_100);
x_138 = l_String_Slice_posGE___redArg(x_1, x_137);
lean_inc(x_138);
x_139 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_139, 0, x_98);
lean_ctor_set(x_139, 1, x_99);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_120);
x_5 = x_139;
x_6 = x_135;
x_7 = x_138;
goto block_15;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_100, x_140);
lean_dec(x_100);
x_142 = lean_nat_add(x_101, x_140);
lean_dec(x_101);
x_143 = lean_nat_sub(x_114, x_113);
x_144 = lean_nat_dec_eq(x_142, x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_145, 0, x_98);
lean_ctor_set(x_145, 1, x_99);
lean_ctor_set(x_145, 2, x_141);
lean_ctor_set(x_145, 3, x_142);
x_3 = x_145;
goto _start;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_142);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_148, 0, x_98);
lean_ctor_set(x_148, 1, x_99);
lean_ctor_set(x_148, 2, x_141);
lean_ctor_set(x_148, 3, x_147);
x_16 = x_148;
goto block_22;
}
}
}
}
}
default: 
{
lean_dec_ref(x_1);
return x_4;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_8 = l_String_Slice_slice_x21(x_1, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_string_utf8_extract(x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_string_append(x_4, x_12);
lean_dec_ref(x_12);
x_3 = x_5;
x_4 = x_13;
goto _start;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_string_utf8_byte_size(x_2);
x_19 = lean_string_utf8_extract(x_2, x_17, x_18);
x_20 = lean_string_append(x_4, x_19);
lean_dec_ref(x_19);
x_3 = x_16;
x_4 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5;
x_3 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1));
x_4 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6;
x_6 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7));
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_string_utf8_byte_size(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_10, x_1);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_internal_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_3 = l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_FFI_getInternalCFlags(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lean_get_linker_flags(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_get_linker_flags(x_1);
x_3 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__0));
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__1));
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = ((lean_object*)(l_Lean_Compiler_FFI_getLinkerFlags___closed__2));
x_6 = l_System_FilePath_join(x_4, x_5);
x_7 = l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_2);
x_10 = l_Array_append___redArg(x_8, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Compiler_FFI_getLinkerFlags(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_internal_linker_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_internal_linker_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_3 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags(x_1);
lean_dec_ref(x_1);
return x_2;
}
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
l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0 = _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0);
l_Lean_Compiler_FFI_getCFlags_x27___closed__0 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
l_Lean_Compiler_FFI_getCFlags_x27___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
l_Lean_Compiler_FFI_getCFlags_x27 = _init_l_Lean_Compiler_FFI_getCFlags_x27();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27);
l_Lean_Compiler_FFI_getCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getCFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__2);
l_Lean_Compiler_FFI_getCFlags___closed__3 = _init_l_Lean_Compiler_FFI_getCFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__3);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3();
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
l_Lean_Compiler_FFI_getInternalCFlags___closed__0 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
l_Lean_Compiler_FFI_getInternalCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
l_Lean_Compiler_FFI_getInternalCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2();
l_Lean_Compiler_FFI_getLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
