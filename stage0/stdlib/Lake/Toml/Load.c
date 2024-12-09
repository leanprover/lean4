// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Lake.Toml.Elab Lake.Util.Message
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
static uint8_t l_Lake_Toml_loadToml___lambda__2___closed__22;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__14;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__21;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__9;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__18;
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__8;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__20;
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
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__13;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_array_mk(lean_object*);
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
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__15;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__16;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__18() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_3 = l_Lean_NameSet_empty;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__16;
x_3 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___lambda__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__21;
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
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
x_55 = l_Lake_Toml_loadToml___lambda__2___closed__14;
x_56 = l_Lake_Toml_loadToml___lambda__2___closed__17;
x_57 = l_Lake_Toml_loadToml___lambda__2___closed__18;
x_58 = l_Lake_Toml_loadToml___lambda__2___closed__19;
x_59 = l_Lake_Toml_loadToml___lambda__2___closed__20;
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_mk_ref(x_60, x_3);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_62, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Kernel_isDiagnosticsEnabled(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
uint8_t x_139; 
x_139 = l_Lake_Toml_loadToml___lambda__2___closed__22;
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = 1;
x_69 = x_140;
goto block_138;
}
else
{
x_69 = x_51;
goto block_138;
}
}
else
{
uint8_t x_141; 
x_141 = l_Lake_Toml_loadToml___lambda__2___closed__22;
if (x_141 == 0)
{
x_69 = x_51;
goto block_138;
}
else
{
uint8_t x_142; 
x_142 = 1;
x_69 = x_142;
goto block_138;
}
}
block_138:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_st_ref_take(x_62, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 4);
lean_dec(x_75);
x_76 = l_Lake_Toml_loadToml___lambda__2___closed__22;
x_77 = l_Lean_Kernel_enableDiag(x_74, x_76);
lean_ctor_set(x_71, 4, x_56);
lean_ctor_set(x_71, 0, x_77);
x_78 = lean_st_ref_set(x_62, x_71, x_72);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
lean_inc(x_62);
x_81 = l_Lake_Toml_loadToml___lambda__1(x_26, x_76, x_42, x_80, x_52, x_62, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_62, x_83);
lean_dec(x_62);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_ctor_set(x_84, 1, x_86);
lean_ctor_set(x_84, 0, x_82);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_84);
x_4 = x_88;
x_5 = x_87;
goto block_23;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_4 = x_92;
x_5 = x_90;
goto block_23;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_62);
x_93 = lean_ctor_get(x_81, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
lean_dec(x_81);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_4 = x_95;
x_5 = x_94;
goto block_23;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_71, 0);
x_97 = lean_ctor_get(x_71, 1);
x_98 = lean_ctor_get(x_71, 2);
x_99 = lean_ctor_get(x_71, 3);
x_100 = lean_ctor_get(x_71, 5);
x_101 = lean_ctor_get(x_71, 6);
x_102 = lean_ctor_get(x_71, 7);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_71);
x_103 = l_Lake_Toml_loadToml___lambda__2___closed__22;
x_104 = l_Lean_Kernel_enableDiag(x_96, x_103);
x_105 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_98);
lean_ctor_set(x_105, 3, x_99);
lean_ctor_set(x_105, 4, x_56);
lean_ctor_set(x_105, 5, x_100);
lean_ctor_set(x_105, 6, x_101);
lean_ctor_set(x_105, 7, x_102);
x_106 = lean_st_ref_set(x_62, x_105, x_72);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_box(0);
lean_inc(x_62);
x_109 = l_Lake_Toml_loadToml___lambda__1(x_26, x_103, x_42, x_108, x_52, x_62, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_st_ref_get(x_62, x_111);
lean_dec(x_62);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_113);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_4 = x_117;
x_5 = x_114;
goto block_23;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_62);
x_118 = lean_ctor_get(x_109, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
lean_dec(x_109);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_4 = x_120;
x_5 = x_119;
goto block_23;
}
}
}
else
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_121 = l_Lake_Toml_loadToml___lambda__2___closed__22;
x_122 = lean_box(0);
lean_inc(x_62);
x_123 = l_Lake_Toml_loadToml___lambda__1(x_26, x_121, x_42, x_122, x_52, x_62, x_66);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_st_ref_get(x_62, x_125);
lean_dec(x_62);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_ctor_set(x_126, 1, x_128);
lean_ctor_set(x_126, 0, x_124);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_126);
x_4 = x_130;
x_5 = x_129;
goto block_23;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_126);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_4 = x_134;
x_5 = x_132;
goto block_23;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_62);
x_135 = lean_ctor_get(x_123, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_123, 1);
lean_inc(x_136);
lean_dec(x_123);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_4 = x_137;
x_5 = x_136;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_29);
lean_dec(x_2);
x_143 = lean_ctor_get(x_33, 0);
lean_inc(x_143);
lean_dec(x_33);
x_144 = l_Lake_mkParserErrorMessage(x_1, x_32, x_143);
lean_dec(x_32);
x_145 = l_Lean_MessageLog_empty;
x_146 = l_Lean_MessageLog_add(x_144, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_3);
return x_147;
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
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__20);
l_Lake_Toml_loadToml___lambda__2___closed__21 = _init_l_Lake_Toml_loadToml___lambda__2___closed__21();
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__21);
l_Lake_Toml_loadToml___lambda__2___closed__22 = _init_l_Lake_Toml_loadToml___lambda__2___closed__22();
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
