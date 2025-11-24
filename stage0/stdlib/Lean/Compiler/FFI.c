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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
lean_object* lean_get_linker_flags(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0;
static lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_get_leanc_extra_flags(lean_object*);
lean_object* l_String_Slice_replaceStartEnd_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object*);
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object*);
static lean_object* l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object*);
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
static size_t l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__0;
lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object*, lean_object*);
static lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_get_leanc_internal_flags(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 32;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get_uint32(x_17, sizeof(void*)*1);
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_nat_sub(x_24, x_23);
x_26 = lean_nat_dec_eq(x_20, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_27 = l_String_Slice_Pos_next___redArg(x_1, x_20);
lean_inc(x_27);
lean_ctor_set(x_17, 0, x_27);
x_28 = lean_nat_add(x_23, x_20);
x_29 = lean_string_utf8_get_fast(x_22, x_28);
lean_dec(x_28);
x_30 = lean_uint32_dec_eq(x_29, x_21);
if (x_30 == 0)
{
lean_dec(x_27);
lean_dec(x_20);
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_1);
x_32 = l_String_Slice_replaceStartEnd_x21(x_1, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_35);
lean_dec_ref(x_32);
lean_ctor_set(x_2, 0, x_27);
x_4 = x_2;
x_5 = x_33;
x_6 = x_34;
x_7 = x_35;
goto block_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_17);
lean_dec(x_20);
lean_free_object(x_2);
x_36 = lean_nat_add(x_23, x_19);
lean_dec(x_19);
x_37 = lean_box(1);
lean_inc(x_24);
lean_inc_ref(x_22);
x_4 = x_37;
x_5 = x_22;
x_6 = x_36;
x_7 = x_24;
goto block_15;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint32_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get_uint32(x_17, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_nat_sub(x_43, x_42);
x_45 = lean_nat_dec_eq(x_39, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_46 = l_String_Slice_Pos_next___redArg(x_1, x_39);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint32(x_47, sizeof(void*)*1, x_40);
x_48 = lean_nat_add(x_42, x_39);
x_49 = lean_string_utf8_get_fast(x_41, x_48);
lean_dec(x_48);
x_50 = lean_uint32_dec_eq(x_49, x_40);
if (x_50 == 0)
{
lean_dec(x_46);
lean_dec(x_39);
lean_ctor_set(x_2, 1, x_47);
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_1);
x_52 = l_String_Slice_replaceStartEnd_x21(x_1, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
lean_dec_ref(x_52);
lean_ctor_set(x_2, 1, x_47);
lean_ctor_set(x_2, 0, x_46);
x_4 = x_2;
x_5 = x_53;
x_6 = x_54;
x_7 = x_55;
goto block_15;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_free_object(x_2);
x_56 = lean_nat_add(x_42, x_38);
lean_dec(x_38);
x_57 = lean_box(1);
lean_inc(x_43);
lean_inc_ref(x_41);
x_4 = x_57;
x_5 = x_41;
x_6 = x_56;
x_7 = x_43;
goto block_15;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint32_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint32(x_58, sizeof(void*)*1);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 2);
x_66 = lean_nat_sub(x_65, x_64);
x_67 = lean_nat_dec_eq(x_60, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint32_t x_71; uint8_t x_72; 
x_68 = l_String_Slice_Pos_next___redArg(x_1, x_60);
lean_inc(x_68);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 1, 4);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint32(x_69, sizeof(void*)*1, x_61);
x_70 = lean_nat_add(x_64, x_60);
x_71 = lean_string_utf8_get_fast(x_63, x_70);
lean_dec(x_70);
x_72 = lean_uint32_dec_eq(x_71, x_61);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_60);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_69);
x_2 = x_73;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc_ref(x_1);
x_75 = l_String_Slice_replaceStartEnd_x21(x_1, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 2);
lean_inc(x_78);
lean_dec_ref(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_69);
x_4 = x_79;
x_5 = x_76;
x_6 = x_77;
x_7 = x_78;
goto block_15;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_62);
lean_dec(x_60);
x_80 = lean_nat_add(x_64, x_59);
lean_dec(x_59);
x_81 = lean_box(1);
lean_inc(x_65);
lean_inc_ref(x_63);
x_4 = x_81;
x_5 = x_63;
x_6 = x_80;
x_7 = x_65;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
block_15:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_12 = lean_array_push(x_3, x_11);
x_2 = x_4;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0;
x_4 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_4);
x_6 = l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
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
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-I", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include", 7, 7);
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
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__0;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__1;
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = l_String_Slice_Pos_next___redArg(x_1, x_38);
lean_inc(x_39);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_39);
x_5 = x_3;
x_6 = x_38;
x_7 = x_39;
goto block_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_3, 0);
lean_inc(x_40);
lean_dec(x_3);
x_41 = l_String_Slice_Pos_next___redArg(x_1, x_40);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_5 = x_42;
x_6 = x_40;
x_7 = x_41;
goto block_15;
}
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 3);
lean_inc(x_46);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_47 = x_3;
} else {
 lean_dec_ref(x_3);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_ctor_get(x_1, 2);
x_51 = lean_nat_sub(x_50, x_49);
x_52 = lean_nat_dec_lt(x_45, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_47);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_lt(x_53, x_46);
if (x_54 == 0)
{
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_45);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_nat_sub(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_56 = l_String_Slice_pos_x21(x_1, x_55);
lean_dec(x_55);
x_57 = lean_box(3);
x_5 = x_57;
x_6 = x_56;
x_7 = x_51;
goto block_15;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
lean_dec(x_51);
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 1);
x_60 = lean_ctor_get(x_43, 2);
x_61 = lean_nat_add(x_49, x_45);
x_62 = lean_string_get_byte_fast(x_48, x_61);
x_63 = lean_nat_add(x_59, x_46);
x_64 = lean_string_get_byte_fast(x_58, x_63);
x_65 = lean_uint8_dec_eq(x_62, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_46, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_46, x_68);
x_70 = lean_array_fget_borrowed(x_44, x_69);
lean_dec(x_69);
x_71 = lean_nat_dec_eq(x_70, x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_70);
x_72 = lean_nat_sub(x_45, x_46);
lean_dec(x_46);
x_73 = l_String_Slice_pos_x21(x_1, x_72);
lean_dec(x_72);
x_74 = lean_nat_sub(x_45, x_70);
x_75 = l_String_Slice_pos_x21(x_1, x_74);
lean_dec(x_74);
if (lean_is_scalar(x_47)) {
 x_76 = lean_alloc_ctor(2, 4, 0);
} else {
 x_76 = x_47;
}
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_44);
lean_ctor_set(x_76, 2, x_45);
lean_ctor_set(x_76, 3, x_70);
x_5 = x_76;
x_6 = x_73;
x_7 = x_75;
goto block_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_82; 
x_77 = lean_nat_sub(x_45, x_46);
lean_dec(x_46);
x_78 = l_String_Slice_pos_x21(x_1, x_77);
lean_dec(x_77);
lean_inc(x_45);
x_82 = l_String_Slice_pos_x3f(x_1, x_45);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_nat_add(x_45, x_68);
lean_dec(x_45);
x_84 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_83);
x_79 = x_84;
goto block_81;
}
else
{
lean_object* x_85; 
lean_dec(x_45);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec_ref(x_82);
x_79 = x_85;
goto block_81;
}
block_81:
{
lean_object* x_80; 
lean_inc(x_79);
if (lean_is_scalar(x_47)) {
 x_80 = lean_alloc_ctor(2, 4, 0);
} else {
 x_80 = x_47;
}
lean_ctor_set(x_80, 0, x_43);
lean_ctor_set(x_80, 1, x_44);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set(x_80, 3, x_66);
x_5 = x_80;
x_6 = x_78;
x_7 = x_79;
goto block_15;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_46);
x_86 = l_String_Slice_pos_x21(x_1, x_45);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_45, x_87);
lean_dec(x_45);
x_89 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_88);
lean_inc(x_89);
if (lean_is_scalar(x_47)) {
 x_90 = lean_alloc_ctor(2, 4, 0);
} else {
 x_90 = x_47;
}
lean_ctor_set(x_90, 0, x_43);
lean_ctor_set(x_90, 1, x_44);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_66);
x_5 = x_90;
x_6 = x_86;
x_7 = x_89;
goto block_15;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_45, x_91);
lean_dec(x_45);
x_93 = lean_nat_add(x_46, x_91);
lean_dec(x_46);
x_94 = lean_nat_sub(x_60, x_59);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
if (lean_is_scalar(x_47)) {
 x_96 = lean_alloc_ctor(2, 4, 0);
} else {
 x_96 = x_47;
}
lean_ctor_set(x_96, 0, x_43);
lean_ctor_set(x_96, 1, x_44);
lean_ctor_set(x_96, 2, x_92);
lean_ctor_set(x_96, 3, x_93);
x_3 = x_96;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_93);
x_98 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_47)) {
 x_99 = lean_alloc_ctor(2, 4, 0);
} else {
 x_99 = x_47;
}
lean_ctor_set(x_99, 0, x_43);
lean_ctor_set(x_99, 1, x_44);
lean_ctor_set(x_99, 2, x_92);
lean_ctor_set(x_99, 3, x_98);
x_16 = x_99;
goto block_22;
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
x_8 = l_String_Slice_replaceStartEnd_x21(x_1, x_6, x_7);
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
lean_dec(x_18);
x_20 = lean_string_append(x_4, x_19);
lean_dec_ref(x_19);
x_3 = x_16;
x_4 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0;
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
x_9 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_8);
x_10 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_6);
x_11 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_3, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_12 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1;
x_13 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_3, x_12, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ROOT", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0;
x_10 = lean_string_utf8_byte_size(x_6);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_11, x_9, x_1);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_12);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0;
x_10 = lean_string_utf8_byte_size(x_6);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_11, x_9, x_1);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_12);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2(x_1, x_2, x_14, x_15);
return x_16;
}
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
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
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getLinkerFlags___closed__0;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2(x_1, x_3, x_4, x_2);
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
l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0 = _init_l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1 = _init_l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__1);
l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0 = _init_l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0();
lean_mark_persistent(l_Std_Iterators_Iter_toStringArray___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___closed__0);
l_Lean_Compiler_FFI_getCFlags_x27___closed__0 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
l_Lean_Compiler_FFI_getCFlags_x27___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
l_Lean_Compiler_FFI_getCFlags_x27 = _init_l_Lean_Compiler_FFI_getCFlags_x27();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27);
l_Lean_Compiler_FFI_getCFlags___closed__0 = _init_l_Lean_Compiler_FFI_getCFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__0);
l_Lean_Compiler_FFI_getCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__1);
l_Lean_Compiler_FFI_getCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getCFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__2);
l_Lean_Compiler_FFI_getCFlags___closed__3 = _init_l_Lean_Compiler_FFI_getCFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__3);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0);
l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1 = _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1();
lean_mark_persistent(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__2_spec__2___closed__0);
l_Lean_Compiler_FFI_getInternalCFlags___closed__0 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
l_Lean_Compiler_FFI_getInternalCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
l_Lean_Compiler_FFI_getInternalCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2();
l_Lean_Compiler_FFI_getLinkerFlags___closed__0 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__0);
l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__2);
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
