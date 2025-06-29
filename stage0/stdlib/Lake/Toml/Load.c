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
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__18;
static lean_object* l_Lake_Toml_loadToml___closed__29;
static lean_object* l_Lake_Toml_loadToml___closed__12;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__17;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__24;
static lean_object* l_Lake_Toml_loadToml___closed__16;
static lean_object* l_Lake_Toml_loadToml___closed__13;
static lean_object* l_Lake_Toml_loadToml___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__3;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lake_Toml_toml;
static lean_object* l_Lake_Toml_loadToml___closed__21;
static lean_object* l_Lake_Toml_loadToml___closed__14;
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__11;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__28;
static lean_object* l_Lake_Toml_loadToml___closed__31;
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
static uint8_t l_Lake_Toml_loadToml___closed__27;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__32;
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lake_Toml_loadToml___closed__30;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lake_Toml_loadToml___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_loadToml___closed__3;
x_2 = l_Lake_Toml_loadToml___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__9;
x_4 = l_Lake_Toml_loadToml___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__14;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__9;
x_4 = l_Lake_Toml_loadToml___closed__16;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__17;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__22() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__9;
x_4 = l_Lake_Toml_loadToml___closed__21;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_Toml_loadToml___closed__26;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__28;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__30;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lake_Toml_toml;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_box(0);
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
x_17 = l_Lake_Toml_loadToml___closed__0;
x_18 = l_Lean_Parser_mkParserState(x_10);
lean_inc(x_1);
x_19 = l_Lean_Parser_ParserFn_run(x_9, x_1, x_16, x_17, x_18);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
x_23 = lean_string_utf8_at_end(x_10, x_22);
lean_dec(x_22);
lean_dec(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_24 = l_Lake_Toml_loadToml___closed__4;
x_25 = l_Lake_mkParserErrorMessage(x_1, x_19, x_24);
lean_dec(x_19);
x_26 = l_Lean_MessageLog_empty;
x_27 = l_Lean_MessageLog_add(x_25, x_26);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_112; uint8_t x_114; 
lean_dec(x_19);
lean_free_object(x_4);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_unsigned_to_nat(2u);
x_31 = l_Lake_Toml_loadToml___closed__7;
x_32 = l_Lake_Toml_loadToml___closed__8;
x_33 = l_Lake_Toml_loadToml___closed__12;
x_34 = l_Lake_Toml_loadToml___closed__15;
x_35 = l_Lake_Toml_loadToml___closed__18;
x_36 = l_Lake_Toml_loadToml___closed__19;
x_37 = l_Lake_Toml_loadToml___closed__20;
x_38 = l_Lake_Toml_loadToml___closed__22;
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_23);
x_40 = l_Lake_Toml_loadToml___closed__23;
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_33);
lean_ctor_set(x_41, 5, x_34);
lean_ctor_set(x_41, 6, x_35);
lean_ctor_set(x_41, 7, x_39);
lean_ctor_set(x_41, 8, x_40);
x_42 = lean_st_mk_ref(x_41, x_7);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lake_Toml_loadToml___closed__24;
x_46 = lean_st_ref_get(x_45, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_43, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Parser_SyntaxStack_back(x_21);
lean_dec(x_21);
x_54 = lean_box(0);
x_55 = l_Lake_Toml_loadToml___closed__25;
x_56 = lean_box(0);
x_57 = lean_box(0);
x_58 = l_Lake_Toml_loadToml___closed__27;
x_114 = l_Lean_Kernel_isDiagnosticsEnabled(x_52);
lean_dec(x_52);
if (x_114 == 0)
{
if (x_58 == 0)
{
x_112 = x_23;
goto block_113;
}
else
{
goto block_111;
}
}
else
{
if (x_58 == 0)
{
goto block_111;
}
else
{
x_112 = x_23;
goto block_113;
}
}
block_89:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_61 = l_Lake_Toml_loadToml___closed__29;
x_62 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_62, 0, x_11);
lean_ctor_set(x_62, 1, x_12);
lean_ctor_set(x_62, 2, x_13);
lean_ctor_set(x_62, 3, x_28);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_54);
lean_ctor_set(x_62, 6, x_14);
lean_ctor_set(x_62, 7, x_15);
lean_ctor_set(x_62, 8, x_28);
lean_ctor_set(x_62, 9, x_55);
lean_ctor_set(x_62, 10, x_29);
lean_ctor_set(x_62, 11, x_57);
lean_ctor_set(x_62, 12, x_47);
lean_ctor_set_uint8(x_62, sizeof(void*)*13, x_58);
x_63 = lean_unbox(x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*13 + 1, x_63);
x_64 = l_Lake_Toml_elabToml(x_53, x_62, x_59, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_43, x_66);
lean_dec(x_43);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 6);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_MessageLog_hasErrors(x_70);
if (x_71 == 0)
{
lean_dec(x_70);
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
else
{
lean_dec(x_65);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_ctor_get(x_72, 6);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MessageLog_hasErrors(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; 
lean_dec(x_65);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_43);
x_78 = !lean_is_exclusive(x_64);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_64, 0);
x_80 = l_Lake_mkExceptionMessage(x_1, x_79);
x_81 = l_Lean_MessageLog_empty;
x_82 = l_Lean_MessageLog_add(x_80, x_81);
lean_ctor_set(x_64, 0, x_82);
return x_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_64, 0);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_64);
x_85 = l_Lake_mkExceptionMessage(x_1, x_83);
x_86 = l_Lean_MessageLog_empty;
x_87 = l_Lean_MessageLog_add(x_85, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
}
block_111:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_st_ref_take(x_43, x_51);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_91, 0);
x_95 = lean_ctor_get(x_91, 5);
lean_dec(x_95);
x_96 = l_Lean_Kernel_enableDiag(x_94, x_58);
lean_ctor_set(x_91, 5, x_34);
lean_ctor_set(x_91, 0, x_96);
x_97 = lean_st_ref_set(x_43, x_91, x_92);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_43);
x_59 = x_43;
x_60 = x_98;
goto block_89;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_99 = lean_ctor_get(x_91, 0);
x_100 = lean_ctor_get(x_91, 1);
x_101 = lean_ctor_get(x_91, 2);
x_102 = lean_ctor_get(x_91, 3);
x_103 = lean_ctor_get(x_91, 4);
x_104 = lean_ctor_get(x_91, 6);
x_105 = lean_ctor_get(x_91, 7);
x_106 = lean_ctor_get(x_91, 8);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_91);
x_107 = l_Lean_Kernel_enableDiag(x_99, x_58);
x_108 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
lean_ctor_set(x_108, 2, x_101);
lean_ctor_set(x_108, 3, x_102);
lean_ctor_set(x_108, 4, x_103);
lean_ctor_set(x_108, 5, x_34);
lean_ctor_set(x_108, 6, x_104);
lean_ctor_set(x_108, 7, x_105);
lean_ctor_set(x_108, 8, x_106);
x_109 = lean_st_ref_set(x_43, x_108, x_92);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_inc(x_43);
x_59 = x_43;
x_60 = x_110;
goto block_89;
}
}
block_113:
{
if (x_112 == 0)
{
goto block_111;
}
else
{
lean_inc(x_43);
x_59 = x_43;
x_60 = x_51;
goto block_89;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_115 = lean_ctor_get(x_20, 0);
lean_inc(x_115);
lean_dec(x_20);
x_116 = l_Lake_mkParserErrorMessage(x_1, x_19, x_115);
lean_dec(x_19);
x_117 = l_Lean_MessageLog_empty;
x_118 = l_Lean_MessageLog_add(x_116, x_117);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_118);
return x_4;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = l_Lake_Toml_toml;
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 2);
lean_inc(x_125);
x_126 = lean_box(0);
x_127 = lean_box(0);
x_128 = lean_box(0);
lean_inc(x_119);
x_129 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_128);
x_130 = l_Lake_Toml_loadToml___closed__0;
x_131 = l_Lean_Parser_mkParserState(x_123);
lean_inc(x_1);
x_132 = l_Lean_Parser_ParserFn_run(x_122, x_1, x_129, x_130, x_131);
x_133 = lean_ctor_get(x_132, 4);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
x_136 = lean_string_utf8_at_end(x_123, x_135);
lean_dec(x_135);
lean_dec(x_123);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_134);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_119);
x_137 = l_Lake_Toml_loadToml___closed__4;
x_138 = l_Lake_mkParserErrorMessage(x_1, x_132, x_137);
lean_dec(x_132);
x_139 = l_Lean_MessageLog_empty;
x_140 = l_Lean_MessageLog_add(x_138, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_120);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; uint8_t x_214; uint8_t x_216; 
lean_dec(x_132);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_unsigned_to_nat(2u);
x_145 = l_Lake_Toml_loadToml___closed__7;
x_146 = l_Lake_Toml_loadToml___closed__8;
x_147 = l_Lake_Toml_loadToml___closed__12;
x_148 = l_Lake_Toml_loadToml___closed__15;
x_149 = l_Lake_Toml_loadToml___closed__18;
x_150 = l_Lake_Toml_loadToml___closed__19;
x_151 = l_Lake_Toml_loadToml___closed__20;
x_152 = l_Lake_Toml_loadToml___closed__22;
x_153 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*3, x_136);
x_154 = l_Lake_Toml_loadToml___closed__23;
x_155 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_155, 0, x_119);
lean_ctor_set(x_155, 1, x_144);
lean_ctor_set(x_155, 2, x_145);
lean_ctor_set(x_155, 3, x_146);
lean_ctor_set(x_155, 4, x_147);
lean_ctor_set(x_155, 5, x_148);
lean_ctor_set(x_155, 6, x_149);
lean_ctor_set(x_155, 7, x_153);
lean_ctor_set(x_155, 8, x_154);
x_156 = lean_st_mk_ref(x_155, x_120);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lake_Toml_loadToml___closed__24;
x_160 = lean_st_ref_get(x_159, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_157, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Parser_SyntaxStack_back(x_134);
lean_dec(x_134);
x_168 = lean_box(0);
x_169 = l_Lake_Toml_loadToml___closed__25;
x_170 = lean_box(0);
x_171 = lean_box(0);
x_172 = l_Lake_Toml_loadToml___closed__27;
x_216 = l_Lean_Kernel_isDiagnosticsEnabled(x_166);
lean_dec(x_166);
if (x_216 == 0)
{
if (x_172 == 0)
{
x_214 = x_136;
goto block_215;
}
else
{
goto block_213;
}
}
else
{
if (x_172 == 0)
{
goto block_213;
}
else
{
x_214 = x_136;
goto block_215;
}
}
block_196:
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_175 = l_Lake_Toml_loadToml___closed__29;
x_176 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_176, 0, x_124);
lean_ctor_set(x_176, 1, x_125);
lean_ctor_set(x_176, 2, x_126);
lean_ctor_set(x_176, 3, x_142);
lean_ctor_set(x_176, 4, x_175);
lean_ctor_set(x_176, 5, x_168);
lean_ctor_set(x_176, 6, x_127);
lean_ctor_set(x_176, 7, x_128);
lean_ctor_set(x_176, 8, x_142);
lean_ctor_set(x_176, 9, x_169);
lean_ctor_set(x_176, 10, x_143);
lean_ctor_set(x_176, 11, x_171);
lean_ctor_set(x_176, 12, x_161);
lean_ctor_set_uint8(x_176, sizeof(void*)*13, x_172);
x_177 = lean_unbox(x_170);
lean_ctor_set_uint8(x_176, sizeof(void*)*13 + 1, x_177);
x_178 = l_Lake_Toml_elabToml(x_167, x_176, x_173, x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_dec(x_1);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_st_ref_get(x_157, x_180);
lean_dec(x_157);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_182, 6);
lean_inc(x_185);
lean_dec(x_182);
x_186 = l_Lean_MessageLog_hasErrors(x_185);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_185);
if (lean_is_scalar(x_184)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_184;
}
lean_ctor_set(x_187, 0, x_179);
lean_ctor_set(x_187, 1, x_183);
return x_187;
}
else
{
lean_object* x_188; 
lean_dec(x_179);
if (lean_is_scalar(x_184)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_184;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_183);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_157);
x_189 = lean_ctor_get(x_178, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_178, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_191 = x_178;
} else {
 lean_dec_ref(x_178);
 x_191 = lean_box(0);
}
x_192 = l_Lake_mkExceptionMessage(x_1, x_189);
x_193 = l_Lean_MessageLog_empty;
x_194 = l_Lean_MessageLog_add(x_192, x_193);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
}
block_213:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_197 = lean_st_ref_take(x_157, x_165);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_198, 6);
lean_inc(x_205);
x_206 = lean_ctor_get(x_198, 7);
lean_inc(x_206);
x_207 = lean_ctor_get(x_198, 8);
lean_inc(x_207);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 lean_ctor_release(x_198, 6);
 lean_ctor_release(x_198, 7);
 lean_ctor_release(x_198, 8);
 x_208 = x_198;
} else {
 lean_dec_ref(x_198);
 x_208 = lean_box(0);
}
x_209 = l_Lean_Kernel_enableDiag(x_200, x_172);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 9, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_201);
lean_ctor_set(x_210, 2, x_202);
lean_ctor_set(x_210, 3, x_203);
lean_ctor_set(x_210, 4, x_204);
lean_ctor_set(x_210, 5, x_148);
lean_ctor_set(x_210, 6, x_205);
lean_ctor_set(x_210, 7, x_206);
lean_ctor_set(x_210, 8, x_207);
x_211 = lean_st_ref_set(x_157, x_210, x_199);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
lean_inc(x_157);
x_173 = x_157;
x_174 = x_212;
goto block_196;
}
block_215:
{
if (x_214 == 0)
{
goto block_213;
}
else
{
lean_inc(x_157);
x_173 = x_157;
x_174 = x_165;
goto block_196;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_119);
x_217 = lean_ctor_get(x_133, 0);
lean_inc(x_217);
lean_dec(x_133);
x_218 = l_Lake_mkParserErrorMessage(x_1, x_132, x_217);
lean_dec(x_132);
x_219 = l_Lean_MessageLog_empty;
x_220 = l_Lean_MessageLog_add(x_218, x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_120);
return x_221;
}
}
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_4);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_223 = lean_ctor_get(x_4, 0);
x_224 = l_Lake_Toml_loadToml___closed__31;
x_225 = lean_io_error_to_string(x_223);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l_Lean_MessageData_ofFormat(x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lake_Toml_loadToml___closed__32;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_box(2);
x_232 = lean_unbox(x_231);
x_233 = l_Lake_mkMessageNoPos(x_1, x_230, x_232);
x_234 = l_Lean_MessageLog_empty;
x_235 = l_Lean_MessageLog_add(x_233, x_234);
lean_ctor_set(x_4, 0, x_235);
return x_4;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_236 = lean_ctor_get(x_4, 0);
x_237 = lean_ctor_get(x_4, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_4);
x_238 = l_Lake_Toml_loadToml___closed__31;
x_239 = lean_io_error_to_string(x_236);
x_240 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = l_Lean_MessageData_ofFormat(x_240);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lake_Toml_loadToml___closed__32;
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_box(2);
x_246 = lean_unbox(x_245);
x_247 = l_Lake_mkMessageNoPos(x_1, x_244, x_246);
x_248 = l_Lean_MessageLog_empty;
x_249 = l_Lean_MessageLog_add(x_247, x_248);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_237);
return x_250;
}
}
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
l_Lake_Toml_loadToml___closed__0 = _init_l_Lake_Toml_loadToml___closed__0();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__0);
l_Lake_Toml_loadToml___closed__1 = _init_l_Lake_Toml_loadToml___closed__1();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__1);
l_Lake_Toml_loadToml___closed__2 = _init_l_Lake_Toml_loadToml___closed__2();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__2);
l_Lake_Toml_loadToml___closed__3 = _init_l_Lake_Toml_loadToml___closed__3();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__3);
l_Lake_Toml_loadToml___closed__4 = _init_l_Lake_Toml_loadToml___closed__4();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__4);
l_Lake_Toml_loadToml___closed__5 = _init_l_Lake_Toml_loadToml___closed__5();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__5);
l_Lake_Toml_loadToml___closed__6 = _init_l_Lake_Toml_loadToml___closed__6();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__6);
l_Lake_Toml_loadToml___closed__7 = _init_l_Lake_Toml_loadToml___closed__7();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__7);
l_Lake_Toml_loadToml___closed__8 = _init_l_Lake_Toml_loadToml___closed__8();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__8);
l_Lake_Toml_loadToml___closed__9 = _init_l_Lake_Toml_loadToml___closed__9();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__9);
l_Lake_Toml_loadToml___closed__10 = _init_l_Lake_Toml_loadToml___closed__10();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__10);
l_Lake_Toml_loadToml___closed__11 = _init_l_Lake_Toml_loadToml___closed__11();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__11);
l_Lake_Toml_loadToml___closed__12 = _init_l_Lake_Toml_loadToml___closed__12();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__12);
l_Lake_Toml_loadToml___closed__13 = _init_l_Lake_Toml_loadToml___closed__13();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__13);
l_Lake_Toml_loadToml___closed__14 = _init_l_Lake_Toml_loadToml___closed__14();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__14);
l_Lake_Toml_loadToml___closed__15 = _init_l_Lake_Toml_loadToml___closed__15();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__15);
l_Lake_Toml_loadToml___closed__16 = _init_l_Lake_Toml_loadToml___closed__16();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__16);
l_Lake_Toml_loadToml___closed__17 = _init_l_Lake_Toml_loadToml___closed__17();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__17);
l_Lake_Toml_loadToml___closed__18 = _init_l_Lake_Toml_loadToml___closed__18();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__18);
l_Lake_Toml_loadToml___closed__19 = _init_l_Lake_Toml_loadToml___closed__19();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__19);
l_Lake_Toml_loadToml___closed__20 = _init_l_Lake_Toml_loadToml___closed__20();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__20);
l_Lake_Toml_loadToml___closed__21 = _init_l_Lake_Toml_loadToml___closed__21();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__21);
l_Lake_Toml_loadToml___closed__22 = _init_l_Lake_Toml_loadToml___closed__22();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__22);
l_Lake_Toml_loadToml___closed__23 = _init_l_Lake_Toml_loadToml___closed__23();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__23);
l_Lake_Toml_loadToml___closed__24 = _init_l_Lake_Toml_loadToml___closed__24();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__24);
l_Lake_Toml_loadToml___closed__25 = _init_l_Lake_Toml_loadToml___closed__25();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__25);
l_Lake_Toml_loadToml___closed__26 = _init_l_Lake_Toml_loadToml___closed__26();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__26);
l_Lake_Toml_loadToml___closed__27 = _init_l_Lake_Toml_loadToml___closed__27();
l_Lake_Toml_loadToml___closed__28 = _init_l_Lake_Toml_loadToml___closed__28();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__28);
l_Lake_Toml_loadToml___closed__29 = _init_l_Lake_Toml_loadToml___closed__29();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__29);
l_Lake_Toml_loadToml___closed__30 = _init_l_Lake_Toml_loadToml___closed__30();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__30);
l_Lake_Toml_loadToml___closed__31 = _init_l_Lake_Toml_loadToml___closed__31();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__31);
l_Lake_Toml_loadToml___closed__32 = _init_l_Lake_Toml_loadToml___closed__32();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__32);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
