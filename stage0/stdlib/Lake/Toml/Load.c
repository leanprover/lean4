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
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__14;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__9;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__18;
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__8;
lean_object* l_Lean_stringToMessageData(lean_object*);
static uint8_t l_Lake_Toml_loadToml___lambda__2___closed__20;
static lean_object* l_Lake_Toml_loadToml___closed__3;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lake_Toml_toml;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__10;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__5;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__16;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__2;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__17;
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__4;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__2;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__15;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__19;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__12;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__7;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__13;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__6;
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__1___closed__1;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lake_Toml_loadToml___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lake_Toml_loadToml___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*12, x_2);
x_13 = l_Lake_Toml_elabToml(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_25 = l_Lake_Toml_loadToml___lambda__1___closed__1;
x_26 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_17);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_24);
x_28 = l_Lake_Toml_elabToml(x_3, x_27, x_6, x_7);
return x_28;
}
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__4;
x_3 = l_Lake_Toml_loadToml___lambda__2___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__9;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__13() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__12;
x_3 = l_Lake_Toml_loadToml___lambda__2___closed__11;
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
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__15;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__18() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__15;
x_3 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__19;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = l_Lake_Toml_toml;
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = lean_box(0);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = l_Lean_Parser_mkParserState(x_29);
x_31 = l_Lake_Toml_loadToml___lambda__2___closed__1;
lean_inc(x_1);
x_32 = l_Lean_Parser_ParserFn_run(x_25, x_1, x_28, x_31, x_30);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_string_utf8_at_end(x_29, x_34);
lean_dec(x_34);
lean_dec(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_36 = l_Lake_Toml_loadToml___lambda__2___closed__5;
x_37 = l_Lake_mkParserErrorMessage(x_1, x_32, x_36);
lean_dec(x_32);
x_38 = l_Lean_MessageLog_empty;
x_39 = l_Lean_MessageLog_add(x_37, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Lean_Parser_SyntaxStack_back(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_unsigned_to_nat(1000u);
x_48 = lean_box(0);
x_49 = l_Lake_Toml_loadToml___lambda__2___closed__6;
x_50 = l_Lean_firstFrontendMacroScope;
x_51 = 0;
x_52 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_26);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_27);
lean_ctor_set(x_52, 7, x_26);
lean_ctor_set(x_52, 8, x_46);
lean_ctor_set(x_52, 9, x_49);
lean_ctor_set(x_52, 10, x_50);
lean_ctor_set(x_52, 11, x_45);
lean_ctor_set_uint8(x_52, sizeof(void*)*12, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*12 + 1, x_51);
x_53 = l_Lake_Toml_loadToml___lambda__2___closed__7;
x_54 = l_Lake_Toml_loadToml___lambda__2___closed__10;
x_55 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_56 = l_Lake_Toml_loadToml___lambda__2___closed__16;
x_57 = l_Lake_Toml_loadToml___lambda__2___closed__17;
x_58 = l_Lake_Toml_loadToml___lambda__2___closed__18;
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_57);
lean_ctor_set(x_59, 6, x_58);
x_60 = lean_st_mk_ref(x_59, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_get(x_61, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Kernel_isDiagnosticsEnabled(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_137; 
x_137 = l_Lake_Toml_loadToml___lambda__2___closed__20;
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = 1;
x_68 = x_138;
goto block_136;
}
else
{
x_68 = x_51;
goto block_136;
}
}
else
{
uint8_t x_139; 
x_139 = l_Lake_Toml_loadToml___lambda__2___closed__20;
if (x_139 == 0)
{
x_68 = x_51;
goto block_136;
}
else
{
uint8_t x_140; 
x_140 = 1;
x_68 = x_140;
goto block_136;
}
}
block_136:
{
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_st_ref_take(x_61, x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 4);
lean_dec(x_74);
x_75 = l_Lake_Toml_loadToml___lambda__2___closed__20;
x_76 = l_Lean_Kernel_enableDiag(x_73, x_75);
lean_ctor_set(x_70, 4, x_56);
lean_ctor_set(x_70, 0, x_76);
x_77 = lean_st_ref_set(x_61, x_70, x_71);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
lean_inc(x_61);
x_80 = l_Lake_Toml_loadToml___lambda__1(x_26, x_75, x_42, x_79, x_52, x_61, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_61, x_82);
lean_dec(x_61);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_ctor_set(x_83, 1, x_85);
lean_ctor_set(x_83, 0, x_81);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_83);
x_4 = x_87;
x_5 = x_86;
goto block_23;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_4 = x_91;
x_5 = x_89;
goto block_23;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_61);
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_dec(x_80);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_4 = x_94;
x_5 = x_93;
goto block_23;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_70, 0);
x_96 = lean_ctor_get(x_70, 1);
x_97 = lean_ctor_get(x_70, 2);
x_98 = lean_ctor_get(x_70, 3);
x_99 = lean_ctor_get(x_70, 5);
x_100 = lean_ctor_get(x_70, 6);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_70);
x_101 = l_Lake_Toml_loadToml___lambda__2___closed__20;
x_102 = l_Lean_Kernel_enableDiag(x_95, x_101);
x_103 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
lean_ctor_set(x_103, 2, x_97);
lean_ctor_set(x_103, 3, x_98);
lean_ctor_set(x_103, 4, x_56);
lean_ctor_set(x_103, 5, x_99);
lean_ctor_set(x_103, 6, x_100);
x_104 = lean_st_ref_set(x_61, x_103, x_71);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_box(0);
lean_inc(x_61);
x_107 = l_Lake_Toml_loadToml___lambda__1(x_26, x_101, x_42, x_106, x_52, x_61, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_get(x_61, x_109);
lean_dec(x_61);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_111);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_4 = x_115;
x_5 = x_112;
goto block_23;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_61);
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
lean_dec(x_107);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_4 = x_118;
x_5 = x_117;
goto block_23;
}
}
}
else
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_119 = l_Lake_Toml_loadToml___lambda__2___closed__20;
x_120 = lean_box(0);
lean_inc(x_61);
x_121 = l_Lake_Toml_loadToml___lambda__1(x_26, x_119, x_42, x_120, x_52, x_61, x_65);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_st_ref_get(x_61, x_123);
lean_dec(x_61);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ctor_get(x_124, 1);
lean_ctor_set(x_124, 1, x_126);
lean_ctor_set(x_124, 0, x_122);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_124);
x_4 = x_128;
x_5 = x_127;
goto block_23;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_124);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_4 = x_132;
x_5 = x_130;
goto block_23;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_61);
x_133 = lean_ctor_get(x_121, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_121, 1);
lean_inc(x_134);
lean_dec(x_121);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_133);
x_4 = x_135;
x_5 = x_134;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_29);
lean_dec(x_2);
x_141 = lean_ctor_get(x_33, 0);
lean_inc(x_141);
lean_dec(x_33);
x_142 = l_Lake_mkParserErrorMessage(x_1, x_32, x_141);
lean_dec(x_32);
x_143 = l_Lean_MessageLog_empty;
x_144 = l_Lean_MessageLog_add(x_142, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_3);
return x_145;
}
block_23:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lake_mkExceptionMessage(x_1, x_6);
x_8 = l_Lean_MessageLog_empty;
x_9 = l_Lean_MessageLog_add(x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_MessageLog_hasErrors(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_dec(x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 5);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_MessageLog_hasErrors(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
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
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_34; lean_object* x_35; 
x_34 = 0;
x_35 = lean_mk_empty_environment(x_34, x_2);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_3 = x_38;
x_4 = x_37;
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_3 = x_41;
x_4 = x_40;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_io_error_to_string(x_6);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_7);
x_8 = l_Lean_MessageData_ofFormat(x_3);
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
x_15 = l_Lean_MessageLog_empty;
x_16 = l_Lean_MessageLog_add(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_io_error_to_string(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = l_Lake_Toml_loadToml___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lake_Toml_loadToml___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 2;
x_27 = l_Lake_mkMessageNoPos(x_1, x_25, x_26);
x_28 = l_Lean_MessageLog_empty;
x_29 = l_Lean_MessageLog_add(x_27, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = l_Lake_Toml_loadToml___lambda__2(x_1, x_31, x_4);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lake_Toml_loadToml___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
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
l_Lake_Toml_loadToml___lambda__2___closed__1 = _init_l_Lake_Toml_loadToml___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__1);
l_Lake_Toml_loadToml___lambda__2___closed__2 = _init_l_Lake_Toml_loadToml___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__2);
l_Lake_Toml_loadToml___lambda__2___closed__3 = _init_l_Lake_Toml_loadToml___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__3);
l_Lake_Toml_loadToml___lambda__2___closed__4 = _init_l_Lake_Toml_loadToml___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__4);
l_Lake_Toml_loadToml___lambda__2___closed__5 = _init_l_Lake_Toml_loadToml___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__5);
l_Lake_Toml_loadToml___lambda__2___closed__6 = _init_l_Lake_Toml_loadToml___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__6);
l_Lake_Toml_loadToml___lambda__2___closed__7 = _init_l_Lake_Toml_loadToml___lambda__2___closed__7();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__7);
l_Lake_Toml_loadToml___lambda__2___closed__8 = _init_l_Lake_Toml_loadToml___lambda__2___closed__8();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__8);
l_Lake_Toml_loadToml___lambda__2___closed__9 = _init_l_Lake_Toml_loadToml___lambda__2___closed__9();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__9);
l_Lake_Toml_loadToml___lambda__2___closed__10 = _init_l_Lake_Toml_loadToml___lambda__2___closed__10();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__10);
l_Lake_Toml_loadToml___lambda__2___closed__11 = _init_l_Lake_Toml_loadToml___lambda__2___closed__11();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__11);
l_Lake_Toml_loadToml___lambda__2___closed__12 = _init_l_Lake_Toml_loadToml___lambda__2___closed__12();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__12);
l_Lake_Toml_loadToml___lambda__2___closed__13 = _init_l_Lake_Toml_loadToml___lambda__2___closed__13();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__13);
l_Lake_Toml_loadToml___lambda__2___closed__14 = _init_l_Lake_Toml_loadToml___lambda__2___closed__14();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__14);
l_Lake_Toml_loadToml___lambda__2___closed__15 = _init_l_Lake_Toml_loadToml___lambda__2___closed__15();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__15);
l_Lake_Toml_loadToml___lambda__2___closed__16 = _init_l_Lake_Toml_loadToml___lambda__2___closed__16();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__16);
l_Lake_Toml_loadToml___lambda__2___closed__17 = _init_l_Lake_Toml_loadToml___lambda__2___closed__17();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__17);
l_Lake_Toml_loadToml___lambda__2___closed__18 = _init_l_Lake_Toml_loadToml___lambda__2___closed__18();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__18);
l_Lake_Toml_loadToml___lambda__2___closed__19 = _init_l_Lake_Toml_loadToml___lambda__2___closed__19();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__19);
l_Lake_Toml_loadToml___lambda__2___closed__20 = _init_l_Lake_Toml_loadToml___lambda__2___closed__20();
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
