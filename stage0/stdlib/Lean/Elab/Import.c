// Lean compiler output
// Module: Lean.Elab.Import
// Imports: Lean.Parser.Module Lean.Data.Json
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
LEAN_EXPORT lean_object* l_IO_println___at_Lean_Elab_printImports___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* lean_print_imports(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_headerToImports___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__2;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__4;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_processHeader___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__5;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_5, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_5, x_11);
lean_dec(x_5);
x_13 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
if (x_10 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_array_uset(x_7, x_2, x_17);
x_2 = x_15;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_uset(x_7, x_2, x_21);
x_2 = x_15;
x_3 = x_22;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_headerToImports___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_headerToImports___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_headerToImports___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_headerToImports___closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1(x_8, x_9, x_7);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_headerToImports___closed__1;
x_12 = l_Array_append___rarg(x_11, x_10);
lean_dec(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Elab_headerToImports___closed__6;
x_14 = l_Array_append___rarg(x_13, x_10);
lean_dec(x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_headerToImports___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_headerToImports(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_processHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_headerToImports(x_1);
x_9 = lean_import_modules(x_8, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = 0;
x_20 = lean_mk_empty_environment(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = 0;
x_24 = l_Lean_Syntax_getPos_x3f(x_1, x_23);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_box(0);
x_28 = lean_io_error_to_string(x_17);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_FileMap_toPosition(x_25, x_31);
x_33 = 2;
x_34 = l_Lean_Elab_processHeader___closed__1;
x_35 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_33);
x_36 = l_Lean_MessageLog_add(x_35, x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_20, 0, x_37);
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_38);
lean_dec(x_24);
x_39 = l_Lean_FileMap_toPosition(x_25, x_38);
lean_dec(x_38);
x_40 = 2;
x_41 = l_Lean_Elab_processHeader___closed__1;
x_42 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_27);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_42, sizeof(void*)*5 + 1, x_40);
x_43 = l_Lean_MessageLog_add(x_42, x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_20, 0, x_44);
return x_20;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = 0;
x_48 = l_Lean_Syntax_getPos_x3f(x_1, x_47);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec(x_4);
x_51 = lean_box(0);
x_52 = lean_io_error_to_string(x_17);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_FileMap_toPosition(x_49, x_55);
x_57 = 2;
x_58 = l_Lean_Elab_processHeader___closed__1;
x_59 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_51);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_47);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_57);
x_60 = l_Lean_MessageLog_add(x_59, x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_46);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_48, 0);
lean_inc(x_63);
lean_dec(x_48);
x_64 = l_Lean_FileMap_toPosition(x_49, x_63);
lean_dec(x_63);
x_65 = 2;
x_66 = l_Lean_Elab_processHeader___closed__1;
x_67 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_51);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_54);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_47);
lean_ctor_set_uint8(x_67, sizeof(void*)*5 + 1, x_65);
x_68 = l_Lean_MessageLog_add(x_67, x_3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_45);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_46);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
return x_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_20, 0);
x_73 = lean_ctor_get(x_20, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_20);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_parseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<input>", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Elab_parseImports___closed__1;
x_5 = 1;
x_6 = l_Lean_Parser_mkInputContext(x_1, x_4, x_5);
lean_inc(x_6);
x_7 = l_Lean_Parser_parseHeader(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = l_Lean_Elab_headerToImports(x_13);
lean_dec(x_13);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_FileMap_toPosition(x_18, x_19);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_20);
lean_ctor_set(x_8, 0, x_17);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Lean_Elab_headerToImports(x_13);
lean_dec(x_13);
x_24 = lean_ctor_get(x_6, 2);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_FileMap_toPosition(x_24, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_8, 0, x_23);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_31 = x_9;
} else {
 lean_dec_ref(x_9);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Elab_headerToImports(x_28);
lean_dec(x_28);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = l_Lean_FileMap_toPosition(x_33, x_34);
lean_dec(x_34);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_40 = x_8;
} else {
 lean_dec_ref(x_8);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_43 = x_9;
} else {
 lean_dec_ref(x_9);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Elab_headerToImports(x_39);
lean_dec(x_39);
x_45 = lean_ctor_get(x_6, 2);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_FileMap_toPosition(x_45, x_46);
lean_dec(x_46);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_40)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_40;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec(x_2);
x_56 = 1;
x_57 = l_Lean_Parser_mkInputContext(x_1, x_55, x_56);
lean_inc(x_57);
x_58 = l_Lean_Parser_parseHeader(x_57, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = l_Lean_Elab_headerToImports(x_64);
lean_dec(x_64);
x_69 = lean_ctor_get(x_57, 2);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_FileMap_toPosition(x_69, x_70);
lean_dec(x_70);
lean_ctor_set(x_60, 0, x_71);
lean_ctor_set(x_59, 0, x_68);
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_60, 0);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_60);
x_74 = l_Lean_Elab_headerToImports(x_64);
lean_dec(x_64);
x_75 = lean_ctor_get(x_57, 2);
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = l_Lean_FileMap_toPosition(x_75, x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_59, 1, x_78);
lean_ctor_set(x_59, 0, x_74);
return x_58;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
lean_dec(x_59);
x_80 = lean_ctor_get(x_60, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_60, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_82 = x_60;
} else {
 lean_dec_ref(x_60);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Elab_headerToImports(x_79);
lean_dec(x_79);
x_84 = lean_ctor_get(x_57, 2);
lean_inc(x_84);
lean_dec(x_57);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
lean_dec(x_80);
x_86 = l_Lean_FileMap_toPosition(x_84, x_85);
lean_dec(x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_58, 0, x_88);
return x_58;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_58, 1);
lean_inc(x_89);
lean_dec(x_58);
x_90 = lean_ctor_get(x_59, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_91 = x_59;
} else {
 lean_dec_ref(x_59);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_60, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_94 = x_60;
} else {
 lean_dec_ref(x_60);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Elab_headerToImports(x_90);
lean_dec(x_90);
x_96 = lean_ctor_get(x_57, 2);
lean_inc(x_96);
lean_dec(x_57);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = l_Lean_FileMap_toPosition(x_96, x_97);
lean_dec(x_97);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_57);
x_102 = !lean_is_exclusive(x_58);
if (x_102 == 0)
{
return x_58;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_58, 0);
x_104 = lean_ctor_get(x_58, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_58);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_Elab_printImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_IO_println___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_findOLean(x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_IO_println___at_Lean_Elab_printImports___spec__1(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_box(0);
x_3 = x_16;
x_4 = x_17;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_parseImports(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = lean_box(0);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2(x_7, x_8, x_9, x_10, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_printImports___spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_headerToImports___closed__1 = _init_l_Lean_Elab_headerToImports___closed__1();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__1);
l_Lean_Elab_headerToImports___closed__2 = _init_l_Lean_Elab_headerToImports___closed__2();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__2);
l_Lean_Elab_headerToImports___closed__3 = _init_l_Lean_Elab_headerToImports___closed__3();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__3);
l_Lean_Elab_headerToImports___closed__4 = _init_l_Lean_Elab_headerToImports___closed__4();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__4);
l_Lean_Elab_headerToImports___closed__5 = _init_l_Lean_Elab_headerToImports___closed__5();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__5);
l_Lean_Elab_headerToImports___closed__6 = _init_l_Lean_Elab_headerToImports___closed__6();
lean_mark_persistent(l_Lean_Elab_headerToImports___closed__6);
l_Lean_Elab_processHeader___closed__1 = _init_l_Lean_Elab_processHeader___closed__1();
lean_mark_persistent(l_Lean_Elab_processHeader___closed__1);
l_Lean_Elab_parseImports___closed__1 = _init_l_Lean_Elab_parseImports___closed__1();
lean_mark_persistent(l_Lean_Elab_parseImports___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
