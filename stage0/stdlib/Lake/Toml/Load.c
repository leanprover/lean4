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
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__22;
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
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__13;
static lean_object* l_Lake_Toml_loadToml___lambda__2___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_array_mk(lean_object*);
static uint8_t l_Lake_Toml_loadToml___lambda__2___closed__23;
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
lean_ctor_set_uint8(x_5, sizeof(void*)*13, x_2);
x_13 = l_Lake_Toml_elabToml(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_5, 12);
lean_inc(x_25);
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
x_26 = l_Lake_Toml_loadToml___lambda__1___closed__1;
x_27 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_26);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set(x_28, 9, x_21);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_23);
lean_ctor_set(x_28, 12, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_24);
x_29 = l_Lake_Toml_elabToml(x_3, x_28, x_6, x_7);
return x_29;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__19() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__16;
x_3 = l_Lake_Toml_loadToml___lambda__2___closed__13;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_1);
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
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___lambda__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___lambda__2___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___lambda__2___closed__22;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_33; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = l_Lake_Toml_toml;
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_box(0);
x_52 = lean_box(0);
lean_inc(x_2);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_51);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = l_Lean_Parser_mkParserState(x_54);
x_56 = l_Lake_Toml_loadToml___lambda__2___closed__1;
lean_inc(x_1);
x_57 = l_Lean_Parser_ParserFn_run(x_50, x_1, x_53, x_56, x_55);
x_58 = lean_ctor_get(x_57, 4);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 2);
lean_inc(x_59);
x_60 = lean_string_utf8_at_end(x_54, x_59);
lean_dec(x_59);
lean_dec(x_54);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_61 = l_Lake_Toml_loadToml___lambda__2___closed__5;
x_62 = l_Lake_mkParserErrorMessage(x_1, x_57, x_61);
lean_dec(x_57);
x_63 = l_Lean_MessageLog_empty;
x_64 = l_Lean_MessageLog_add(x_62, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; 
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
x_67 = l_Lean_Parser_SyntaxStack_back(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
x_70 = lean_box(0);
x_71 = l_Lake_Toml_loadToml___lambda__2___closed__7;
x_72 = l_Lake_Toml_loadToml___lambda__2___closed__10;
x_73 = l_Lake_Toml_loadToml___lambda__2___closed__14;
x_74 = l_Lake_Toml_loadToml___lambda__2___closed__17;
x_75 = l_Lake_Toml_loadToml___lambda__2___closed__18;
x_76 = l_Lake_Toml_loadToml___lambda__2___closed__19;
x_77 = l_Lake_Toml_loadToml___lambda__2___closed__20;
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_74);
lean_ctor_set(x_78, 5, x_75);
lean_ctor_set(x_78, 6, x_76);
lean_ctor_set(x_78, 7, x_77);
x_79 = lean_st_mk_ref(x_78, x_3);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_94 = l_Lake_Toml_loadToml___lambda__2___closed__21;
x_95 = lean_st_ref_get(x_94, x_81);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_unsigned_to_nat(1000u);
x_100 = lean_box(0);
x_101 = l_Lake_Toml_loadToml___lambda__2___closed__6;
x_102 = l_Lean_firstFrontendMacroScope;
x_103 = 0;
x_104 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_104, 0, x_68);
lean_ctor_set(x_104, 1, x_69);
lean_ctor_set(x_104, 2, x_51);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_52);
lean_ctor_set(x_104, 7, x_51);
lean_ctor_set(x_104, 8, x_98);
lean_ctor_set(x_104, 9, x_101);
lean_ctor_set(x_104, 10, x_102);
lean_ctor_set(x_104, 11, x_70);
lean_ctor_set(x_104, 12, x_96);
lean_ctor_set_uint8(x_104, sizeof(void*)*13, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*13 + 1, x_103);
x_105 = lean_st_ref_get(x_80, x_97);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Kernel_isDiagnosticsEnabled(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_159; 
x_159 = l_Lake_Toml_loadToml___lambda__2___closed__23;
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = 1;
x_110 = x_160;
goto block_158;
}
else
{
x_110 = x_103;
goto block_158;
}
}
else
{
uint8_t x_161; 
x_161 = l_Lake_Toml_loadToml___lambda__2___closed__23;
if (x_161 == 0)
{
x_110 = x_103;
goto block_158;
}
else
{
uint8_t x_162; 
x_162 = 1;
x_110 = x_162;
goto block_158;
}
}
block_93:
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_st_ref_get(x_80, x_84);
lean_dec(x_80);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_82;
}
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_85, 0, x_88);
x_33 = x_85;
goto block_48;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_33 = x_92;
goto block_48;
}
}
block_158:
{
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_st_ref_take(x_80, x_107);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_112, 0);
x_116 = lean_ctor_get(x_112, 4);
lean_dec(x_116);
x_117 = l_Lake_Toml_loadToml___lambda__2___closed__23;
x_118 = l_Lean_Kernel_enableDiag(x_115, x_117);
lean_ctor_set(x_112, 4, x_74);
lean_ctor_set(x_112, 0, x_118);
x_119 = lean_st_ref_set(x_80, x_112, x_113);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_box(0);
lean_inc(x_80);
x_122 = l_Lake_Toml_loadToml___lambda__1(x_51, x_117, x_67, x_121, x_104, x_80, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_83 = x_123;
x_84 = x_124;
goto block_93;
}
else
{
uint8_t x_125; 
lean_dec(x_82);
lean_dec(x_80);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
x_33 = x_122;
goto block_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_33 = x_128;
goto block_48;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_129 = lean_ctor_get(x_112, 0);
x_130 = lean_ctor_get(x_112, 1);
x_131 = lean_ctor_get(x_112, 2);
x_132 = lean_ctor_get(x_112, 3);
x_133 = lean_ctor_get(x_112, 5);
x_134 = lean_ctor_get(x_112, 6);
x_135 = lean_ctor_get(x_112, 7);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_112);
x_136 = l_Lake_Toml_loadToml___lambda__2___closed__23;
x_137 = l_Lean_Kernel_enableDiag(x_129, x_136);
x_138 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
lean_ctor_set(x_138, 2, x_131);
lean_ctor_set(x_138, 3, x_132);
lean_ctor_set(x_138, 4, x_74);
lean_ctor_set(x_138, 5, x_133);
lean_ctor_set(x_138, 6, x_134);
lean_ctor_set(x_138, 7, x_135);
x_139 = lean_st_ref_set(x_80, x_138, x_113);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_box(0);
lean_inc(x_80);
x_142 = l_Lake_Toml_loadToml___lambda__1(x_51, x_136, x_67, x_141, x_104, x_80, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_83 = x_143;
x_84 = x_144;
goto block_93;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_82);
lean_dec(x_80);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
x_33 = x_148;
goto block_48;
}
}
}
else
{
uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_149 = l_Lake_Toml_loadToml___lambda__2___closed__23;
x_150 = lean_box(0);
lean_inc(x_80);
x_151 = l_Lake_Toml_loadToml___lambda__1(x_51, x_149, x_67, x_150, x_104, x_80, x_107);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_83 = x_152;
x_84 = x_153;
goto block_93;
}
else
{
uint8_t x_154; 
lean_dec(x_82);
lean_dec(x_80);
x_154 = !lean_is_exclusive(x_151);
if (x_154 == 0)
{
x_33 = x_151;
goto block_48;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_151, 0);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_151);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_33 = x_157;
goto block_48;
}
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_54);
lean_dec(x_2);
x_163 = lean_ctor_get(x_58, 0);
lean_inc(x_163);
lean_dec(x_58);
x_164 = l_Lake_mkParserErrorMessage(x_1, x_57, x_163);
lean_dec(x_57);
x_165 = l_Lean_MessageLog_empty;
x_166 = l_Lean_MessageLog_add(x_164, x_165);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_3);
return x_167;
}
block_32:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lake_mkExceptionMessage(x_1, x_8);
x_10 = l_Lean_MessageLog_empty;
x_11 = l_Lean_MessageLog_add(x_9, x_10);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Lake_mkExceptionMessage(x_1, x_13);
x_15 = l_Lean_MessageLog_empty;
x_16 = l_Lean_MessageLog_add(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 5);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_MessageLog_hasErrors(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_dec(x_21);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_27, 5);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_MessageLog_hasErrors(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
}
block_48:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_33, 0, x_36);
x_4 = x_33;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_4 = x_40;
goto block_32;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_43);
x_4 = x_33;
goto block_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_4 = x_47;
goto block_32;
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
lean_mark_persistent(l_Lake_Toml_loadToml___lambda__2___closed__22);
l_Lake_Toml_loadToml___lambda__2___closed__23 = _init_l_Lake_Toml_loadToml___lambda__2___closed__23();
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
