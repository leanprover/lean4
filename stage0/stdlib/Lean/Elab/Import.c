// Lean compiler output
// Module: Lean.Elab.Import
// Imports: Init Lean.Parser.Module Lean.Data.Json
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__4;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_headerToImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_headerToImports___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports___boxed(lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lean_Elab_parseImports___closed__1;
static lean_object* l_Lean_Elab_headerToImports___closed__3;
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_printImports___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_processHeader___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_print_imports(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at_Lean_Elab_printImports___spec__1(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_headerToImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_5, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_5, x_10);
lean_dec(x_5);
x_12 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
if (x_9 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_19, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_19, x_24);
lean_dec(x_19);
x_26 = l_Lean_Syntax_getId(x_25);
lean_dec(x_25);
if (x_23 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
x_1 = x_20;
x_2 = x_29;
goto _start;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
x_1 = x_20;
x_2 = x_33;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_headerToImports___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_headerToImports___closed__2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_headerToImports___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_headerToImports___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_to_list(lean_box(0), x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at_Lean_Elab_headerToImports___spec__1(x_8, x_9);
if (x_4 == 0)
{
lean_object* x_11; 
x_11 = l_List_appendTR___rarg(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_headerToImports___closed__4;
x_13 = l_List_appendTR___rarg(x_12, x_10);
return x_13;
}
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
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_headerToImports(x_1);
x_8 = lean_import_modules(x_7, x_2, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = 0;
x_19 = lean_mk_empty_environment(x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = 0;
x_23 = l_Lean_Syntax_getPos_x3f(x_1, x_22);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 1);
x_26 = lean_box(0);
x_27 = lean_io_error_to_string(x_16);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_FileMap_toPosition(x_24, x_30);
x_32 = 2;
x_33 = l_Lean_Elab_processHeader___closed__1;
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_32);
x_35 = l_Lean_PersistentArray_push___rarg(x_3, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = l_Lean_FileMap_toPosition(x_24, x_37);
lean_dec(x_37);
x_39 = 2;
x_40 = l_Lean_Elab_processHeader___closed__1;
lean_inc(x_25);
x_41 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_29);
lean_ctor_set_uint8(x_41, sizeof(void*)*5, x_39);
x_42 = l_Lean_PersistentArray_push___rarg(x_3, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = 0;
x_47 = l_Lean_Syntax_getPos_x3f(x_1, x_46);
x_48 = lean_ctor_get(x_4, 2);
x_49 = lean_ctor_get(x_4, 1);
x_50 = lean_box(0);
x_51 = lean_io_error_to_string(x_16);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_FileMap_toPosition(x_48, x_54);
x_56 = 2;
x_57 = l_Lean_Elab_processHeader___closed__1;
lean_inc(x_49);
x_58 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_56);
x_59 = l_Lean_PersistentArray_push___rarg(x_3, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_45);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
x_63 = l_Lean_FileMap_toPosition(x_48, x_62);
lean_dec(x_62);
x_64 = 2;
x_65 = l_Lean_Elab_processHeader___closed__1;
lean_inc(x_49);
x_66 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_50);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_53);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_64);
x_67 = l_Lean_PersistentArray_push___rarg(x_3, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_44);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_45);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_16);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
return x_19;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_19, 0);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_19);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_parseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<input>", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_parseImports___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
x_6 = l_Lean_Parser_parseHeader(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = l_Lean_Elab_headerToImports(x_12);
lean_dec(x_12);
x_17 = l_Lean_FileMap_ofString(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_FileMap_toPosition(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_8, 0, x_19);
lean_ctor_set(x_7, 0, x_16);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Elab_headerToImports(x_12);
lean_dec(x_12);
x_23 = l_Lean_FileMap_ofString(x_1);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_FileMap_toPosition(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_22);
return x_6;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_30 = x_8;
} else {
 lean_dec_ref(x_8);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Elab_headerToImports(x_27);
lean_dec(x_27);
x_32 = l_Lean_FileMap_ofString(x_1);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_FileMap_toPosition(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_6, 0, x_36);
return x_6;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_39 = x_7;
} else {
 lean_dec_ref(x_7);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_42 = x_8;
} else {
 lean_dec_ref(x_8);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Elab_headerToImports(x_38);
lean_dec(x_38);
x_44 = l_Lean_FileMap_ofString(x_1);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l_Lean_FileMap_toPosition(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
if (lean_is_scalar(x_39)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_39;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
lean_inc(x_1);
x_55 = l_Lean_Parser_mkInputContext(x_1, x_54);
x_56 = l_Lean_Parser_parseHeader(x_55, x_3);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = l_Lean_Elab_headerToImports(x_62);
lean_dec(x_62);
x_67 = l_Lean_FileMap_ofString(x_1);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_FileMap_toPosition(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
lean_ctor_set(x_58, 0, x_69);
lean_ctor_set(x_57, 0, x_66);
return x_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
x_72 = l_Lean_Elab_headerToImports(x_62);
lean_dec(x_62);
x_73 = l_Lean_FileMap_ofString(x_1);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lean_FileMap_toPosition(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_57, 1, x_76);
lean_ctor_set(x_57, 0, x_72);
return x_56;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_57, 0);
lean_inc(x_77);
lean_dec(x_57);
x_78 = lean_ctor_get(x_58, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_80 = x_58;
} else {
 lean_dec_ref(x_58);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Elab_headerToImports(x_77);
lean_dec(x_77);
x_82 = l_Lean_FileMap_ofString(x_1);
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec(x_78);
x_84 = l_Lean_FileMap_toPosition(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_56, 0, x_86);
return x_56;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_56, 1);
lean_inc(x_87);
lean_dec(x_56);
x_88 = lean_ctor_get(x_57, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_89 = x_57;
} else {
 lean_dec_ref(x_57);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_58, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_58, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_92 = x_58;
} else {
 lean_dec_ref(x_58);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Elab_headerToImports(x_88);
lean_dec(x_88);
x_94 = l_Lean_FileMap_ofString(x_1);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = l_Lean_FileMap_toPosition(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_87);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_56);
if (x_100 == 0)
{
return x_56;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_56, 0);
x_102 = lean_ctor_get(x_56, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_printImports___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_findOLean(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_println___at_Lean_Elab_printImports___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_1 = x_6;
x_2 = x_13;
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_forIn_loop___at_Lean_Elab_printImports___spec__2(x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Elab_processHeader___closed__1 = _init_l_Lean_Elab_processHeader___closed__1();
lean_mark_persistent(l_Lean_Elab_processHeader___closed__1);
l_Lean_Elab_parseImports___closed__1 = _init_l_Lean_Elab_parseImports___closed__1();
lean_mark_persistent(l_Lean_Elab_parseImports___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
