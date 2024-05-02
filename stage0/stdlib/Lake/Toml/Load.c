// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Init Lake.Toml.Elab Lake.Util.Message
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
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__16;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__13;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__15;
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__3;
extern lean_object* l_Lake_Toml_toml;
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__14;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__19;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__5;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__8;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__12;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__7;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__9;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__18;
uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__17;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__6;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__3;
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__10;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__2;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__1;
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("end of input", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__1___closed__4;
x_3 = l_Lake_Toml_loadToml___lambda__1___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__9;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__13() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lake_Toml_loadToml___lambda__1___closed__12;
x_3 = l_Lake_Toml_loadToml___lambda__1___closed__11;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__16;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__19() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Toml_loadToml___lambda__1___closed__18;
x_3 = l_Lake_Toml_loadToml___lambda__1___closed__13;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = l_Lake_Toml_toml;
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_box(0);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = l_Lean_Parser_mkParserState(x_24);
x_26 = l_Lake_Toml_loadToml___lambda__1___closed__1;
lean_inc(x_1);
x_27 = l_Lean_Parser_ParserFn_run(x_20, x_1, x_23, x_26, x_25);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_string_utf8_at_end(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_31 = l_Lake_Toml_loadToml___lambda__1___closed__5;
x_32 = l_Lake_mkParserErrorMessage(x_1, x_27, x_31);
lean_dec(x_27);
lean_dec(x_1);
x_33 = l_Lean_MessageLog_empty;
x_34 = l_Lean_PersistentArray_push___rarg(x_33, x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l_Lean_Parser_SyntaxStack_back(x_36);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_unsigned_to_nat(1000u);
x_42 = lean_box(0);
x_43 = l_Lake_Toml_loadToml___lambda__1___closed__6;
x_44 = l_Lean_firstFrontendMacroScope;
x_45 = 0;
x_46 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_21);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_22);
lean_ctor_set(x_46, 7, x_21);
lean_ctor_set(x_46, 8, x_40);
lean_ctor_set(x_46, 9, x_43);
lean_ctor_set(x_46, 10, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*11, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*11 + 1, x_45);
x_47 = l_Lake_Toml_loadToml___lambda__1___closed__7;
x_48 = l_Lake_Toml_loadToml___lambda__1___closed__10;
x_49 = l_Lake_Toml_loadToml___lambda__1___closed__13;
x_50 = l_Lake_Toml_loadToml___lambda__1___closed__17;
x_51 = l_Lake_Toml_loadToml___lambda__1___closed__19;
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_51);
x_53 = lean_st_mk_ref(x_52, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_54);
x_56 = l_Lake_Toml_elabToml(x_37, x_46, x_54, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_54, x_58);
lean_dec(x_54);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_4 = x_63;
x_5 = x_61;
goto block_18;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_4 = x_66;
x_5 = x_65;
goto block_18;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_24);
lean_dec(x_2);
x_67 = lean_ctor_get(x_28, 0);
lean_inc(x_67);
lean_dec(x_28);
x_68 = l_Lake_mkParserErrorMessage(x_1, x_27, x_67);
lean_dec(x_27);
lean_dec(x_1);
x_69 = l_Lean_MessageLog_empty;
x_70 = l_Lean_PersistentArray_push___rarg(x_69, x_68);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_3);
return x_71;
}
block_18:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lake_mkExceptionMessage(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_MessageLog_empty;
x_9 = l_Lean_PersistentArray_push___rarg(x_8, x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 5);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to initialize TOML environment: ", 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = lean_mk_empty_environment(x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_3 = x_25;
x_4 = x_24;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_3 = x_28;
x_4 = x_27;
goto block_20;
}
block_20:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_error_to_string(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lake_Toml_loadToml___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lake_Toml_loadToml___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 2;
x_14 = l_Lake_mkMessageNoPos(x_1, x_12, x_13);
lean_dec(x_1);
x_15 = l_Lean_MessageLog_empty;
x_16 = l_Lean_PersistentArray_push___rarg(x_15, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lake_Toml_loadToml___lambda__1(x_1, x_18, x_4);
return x_19;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_loadToml___lambda__1___closed__1 = _init_l_Lake_Toml_loadToml___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__1);
l_Lake_Toml_loadToml___lambda__1___closed__2 = _init_l_Lake_Toml_loadToml___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__2);
l_Lake_Toml_loadToml___lambda__1___closed__3 = _init_l_Lake_Toml_loadToml___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__3);
l_Lake_Toml_loadToml___lambda__1___closed__4 = _init_l_Lake_Toml_loadToml___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__4);
l_Lake_Toml_loadToml___lambda__1___closed__5 = _init_l_Lake_Toml_loadToml___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__5);
l_Lake_Toml_loadToml___lambda__1___closed__6 = _init_l_Lake_Toml_loadToml___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__6);
l_Lake_Toml_loadToml___lambda__1___closed__7 = _init_l_Lake_Toml_loadToml___lambda__1___closed__7();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__7);
l_Lake_Toml_loadToml___lambda__1___closed__8 = _init_l_Lake_Toml_loadToml___lambda__1___closed__8();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__8);
l_Lake_Toml_loadToml___lambda__1___closed__9 = _init_l_Lake_Toml_loadToml___lambda__1___closed__9();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__9);
l_Lake_Toml_loadToml___lambda__1___closed__10 = _init_l_Lake_Toml_loadToml___lambda__1___closed__10();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__10);
l_Lake_Toml_loadToml___lambda__1___closed__11 = _init_l_Lake_Toml_loadToml___lambda__1___closed__11();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__11);
l_Lake_Toml_loadToml___lambda__1___closed__12 = _init_l_Lake_Toml_loadToml___lambda__1___closed__12();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__12);
l_Lake_Toml_loadToml___lambda__1___closed__13 = _init_l_Lake_Toml_loadToml___lambda__1___closed__13();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__13);
l_Lake_Toml_loadToml___lambda__1___closed__14 = _init_l_Lake_Toml_loadToml___lambda__1___closed__14();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__14);
l_Lake_Toml_loadToml___lambda__1___closed__15 = _init_l_Lake_Toml_loadToml___lambda__1___closed__15();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__15);
l_Lake_Toml_loadToml___lambda__1___closed__16 = _init_l_Lake_Toml_loadToml___lambda__1___closed__16();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__16);
l_Lake_Toml_loadToml___lambda__1___closed__17 = _init_l_Lake_Toml_loadToml___lambda__1___closed__17();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__17);
l_Lake_Toml_loadToml___lambda__1___closed__18 = _init_l_Lake_Toml_loadToml___lambda__1___closed__18();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__18);
l_Lake_Toml_loadToml___lambda__1___closed__19 = _init_l_Lake_Toml_loadToml___lambda__1___closed__19();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__1___closed__19);
l_Lake_Toml_loadToml___closed__1 = _init_l_Lake_Toml_loadToml___closed__1();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__1);
l_Lake_Toml_loadToml___closed__2 = _init_l_Lake_Toml_loadToml___closed__2();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__2);
l_Lake_Toml_loadToml___closed__3 = _init_l_Lake_Toml_loadToml___closed__3();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
