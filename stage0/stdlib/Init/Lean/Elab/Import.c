// Lean compiler output
// Module: Init.Lean.Elab.Import
// Imports: Init.Lean.Parser.Module
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_headerToImports___closed__4;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_headerToImports___spec__1(lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_headerToImports___closed__2;
lean_object* l_Lean_Elab_headerToImports(lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_headerToImports___closed__1;
lean_object* l_Lean_Elab_headerToImports___boxed(lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Elab_headerToImports___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_HasRepr_HasEval___spec__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* lean_print_deps(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_import_modules(lean_object*, uint32_t, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l_Lean_normalizeModuleName___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_parse_imports(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_printDeps___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
extern lean_object* l_Lean_getBuiltinSearchPath___closed__3;
lean_object* lean_normalize_module_name(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_headerToImports___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getIdAt(x_4, x_9);
lean_dec(x_4);
x_11 = lean_normalize_module_name(x_10);
x_12 = l_List_map___main___at_Lean_Elab_headerToImports___spec__1(x_5);
if (x_8 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_17, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getIdAt(x_17, x_22);
lean_dec(x_17);
x_24 = lean_normalize_module_name(x_23);
x_25 = l_List_map___main___at_Lean_Elab_headerToImports___spec__1(x_18);
if (x_21 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_headerToImports___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getBuiltinSearchPath___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_headerToImports___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_headerToImports___closed__1;
x_2 = l_Lean_normalizeModuleName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_headerToImports___closed__3() {
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
lean_object* _init_l_Lean_Elab_headerToImports___closed__4() {
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
lean_object* l_Lean_Elab_headerToImports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_2 = l_Lean_Syntax_asNode(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_3, x_5);
x_7 = l_Lean_Syntax_isNone(x_6);
lean_dec(x_6);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_4, x_3, x_10);
lean_dec(x_3);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = l_Array_toList___rarg(x_12);
lean_dec(x_12);
x_14 = l_List_map___main___at_Lean_Elab_headerToImports___spec__1(x_13);
x_15 = l_List_append___rarg(x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_array_get(x_4, x_3, x_16);
lean_dec(x_3);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_20 = l_List_map___main___at_Lean_Elab_headerToImports___spec__1(x_19);
x_21 = l_Lean_Elab_headerToImports___closed__4;
x_22 = l_List_append___rarg(x_21, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Elab_headerToImports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_headerToImports(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_headerToImports(x_1);
x_7 = lean_import_modules(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 0;
x_18 = lean_mk_empty_environment(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Syntax_getPos(x_1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_box(0);
x_25 = lean_io_error_to_string(x_15);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_FileMap_toPosition(x_22, x_28);
x_30 = 2;
x_31 = l_String_splitAux___main___closed__1;
lean_inc(x_23);
x_32 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*5, x_30);
x_33 = l_PersistentArray_push___rarg(x_2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_18, 0, x_34);
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = l_Lean_FileMap_toPosition(x_22, x_35);
lean_dec(x_35);
x_37 = 2;
x_38 = l_String_splitAux___main___closed__1;
lean_inc(x_23);
x_39 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_24);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_27);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_37);
x_40 = l_PersistentArray_push___rarg(x_2, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_18, 0, x_41);
return x_18;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = l_Lean_Syntax_getPos(x_1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_box(0);
x_48 = lean_io_error_to_string(x_15);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_FileMap_toPosition(x_45, x_51);
x_53 = 2;
x_54 = l_String_splitAux___main___closed__1;
lean_inc(x_46);
x_55 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*5, x_53);
x_56 = l_PersistentArray_push___rarg(x_2, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_42);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
lean_dec(x_44);
x_60 = l_Lean_FileMap_toPosition(x_45, x_59);
lean_dec(x_59);
x_61 = 2;
x_62 = l_String_splitAux___main___closed__1;
lean_inc(x_46);
x_63 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_47);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_63, 4, x_50);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_61);
x_64 = l_PersistentArray_push___rarg(x_2, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_43);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
lean_object* l_Lean_Elab_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_parseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<input>");
return x_1;
}
}
lean_object* l_Lean_Elab_parseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_mk_empty_environment(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Elab_parseImports___closed__1;
lean_inc(x_1);
x_9 = l_Lean_Parser_mkInputContext(x_1, x_8);
x_10 = l_Lean_Parser_parseHeader(x_7, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_Elab_headerToImports(x_14);
lean_dec(x_14);
x_17 = l_Lean_FileMap_ofString(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_FileMap_toPosition(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = l_Lean_Elab_headerToImports(x_20);
lean_dec(x_20);
x_24 = l_Lean_FileMap_ofString(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_FileMap_toPosition(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_23);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_10, 1);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = l_Lean_Elab_headerToImports(x_29);
lean_dec(x_29);
x_34 = l_Lean_FileMap_ofString(x_1);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_FileMap_toPosition(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_5, 0, x_38);
return x_5;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = l_Lean_Elab_parseImports___closed__1;
lean_inc(x_1);
x_42 = l_Lean_Parser_mkInputContext(x_1, x_41);
x_43 = l_Lean_Parser_parseHeader(x_39, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Elab_headerToImports(x_45);
lean_dec(x_45);
x_51 = l_Lean_FileMap_ofString(x_1);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lean_FileMap_toPosition(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
if (lean_is_scalar(x_46)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_46;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l_Lean_Parser_mkInputContext(x_1, x_59);
x_61 = l_Lean_Parser_parseHeader(x_58, x_60);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_63, 0);
x_67 = l_Lean_Elab_headerToImports(x_65);
lean_dec(x_65);
x_68 = l_Lean_FileMap_ofString(x_1);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_FileMap_toPosition(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
lean_ctor_set(x_63, 0, x_70);
lean_ctor_set(x_61, 0, x_67);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = l_Lean_Elab_headerToImports(x_71);
lean_dec(x_71);
x_75 = l_Lean_FileMap_ofString(x_1);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = l_Lean_FileMap_toPosition(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_61, 1, x_78);
lean_ctor_set(x_61, 0, x_74);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_79 = lean_ctor_get(x_61, 1);
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
lean_inc(x_80);
lean_dec(x_61);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Elab_headerToImports(x_80);
lean_dec(x_80);
x_85 = l_Lean_FileMap_ofString(x_1);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_87 = l_Lean_FileMap_toPosition(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_5, 0, x_89);
return x_5;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_5);
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
lean_inc(x_1);
x_93 = l_Lean_Parser_mkInputContext(x_1, x_92);
x_94 = l_Lean_Parser_parseHeader(x_90, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
 x_100 = lean_box(0);
}
x_101 = l_Lean_Elab_headerToImports(x_96);
lean_dec(x_96);
x_102 = l_Lean_FileMap_ofString(x_1);
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
lean_dec(x_98);
x_104 = l_Lean_FileMap_toPosition(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (lean_is_scalar(x_100)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_100;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_97;
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_91);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_5);
if (x_108 == 0)
{
return x_5;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_5, 0);
x_110 = lean_ctor_get(x_5, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_5);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
lean_object* lean_parse_imports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_parseImports(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = l_Lean_MessageLog_toList(x_12);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = l_Lean_MessageLog_toList(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_5, 1, x_17);
return x_4;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_21 = x_6;
} else {
 lean_dec_ref(x_6);
 x_21 = lean_box(0);
}
x_22 = l_Lean_MessageLog_toList(x_20);
lean_dec(x_20);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_30 = x_6;
} else {
 lean_dec_ref(x_6);
 x_30 = lean_box(0);
}
x_31 = l_Lean_MessageLog_toList(x_29);
lean_dec(x_29);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_27)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_27;
}
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_printDeps___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_findOLean(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_println___at_Lean_HasRepr_HasEval___spec__1(x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
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
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* lean_print_deps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forM___main___at_Lean_Elab_printDeps___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_Parser_Module(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Import(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Module(lean_io_mk_world());
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
l_Lean_Elab_parseImports___closed__1 = _init_l_Lean_Elab_parseImports___closed__1();
lean_mark_persistent(l_Lean_Elab_parseImports___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
