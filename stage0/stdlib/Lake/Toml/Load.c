// Lean compiler output
// Module: Lake.Toml.Load
// Imports: public import Lean.Parser.Types public import Lake.Toml.Data.Value import Lean.Parser import Lake.Toml.Elab import Lake.Util.Message
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
static lean_object* l_Lake_Toml_loadToml___closed__12;
static lean_object* l_Lake_Toml_loadToml___closed__17;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__24;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__28;
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
static lean_object* l_Lake_Toml_loadToml___closed__27;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_toml;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_empty;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_loadToml___closed__5;
x_2 = l_Lake_Toml_loadToml___closed__3;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__7;
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12() {
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
static lean_object* _init_l_Lake_Toml_loadToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__13;
x_4 = l_Lake_Toml_loadToml___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__18;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__20;
x_2 = l_Lake_Toml_loadToml___closed__15;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_Toml_loadToml___closed__0;
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = l_Lake_Toml_loadToml___closed__1;
x_16 = l_Lean_Parser_mkParserState(x_9);
lean_inc_ref(x_1);
x_17 = l_Lean_Parser_ParserFn_run(x_8, x_1, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lake_mkParserErrorMessage(x_1, x_17, x_19);
lean_dec_ref(x_17);
x_21 = l_Lake_Toml_loadToml___closed__2;
x_22 = l_Lean_MessageLog_add(x_20, x_21);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_23 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = l_Lean_Parser_InputContext_atEnd(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_23);
lean_dec(x_6);
x_26 = l_Lake_Toml_loadToml___closed__6;
x_27 = l_Lake_mkParserErrorMessage(x_1, x_17, x_26);
lean_dec_ref(x_17);
x_28 = l_Lake_Toml_loadToml___closed__2;
x_29 = l_Lean_MessageLog_add(x_27, x_28);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_29);
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_96; uint8_t x_115; 
lean_dec_ref(x_17);
lean_free_object(x_4);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lake_Toml_loadToml___closed__7;
x_32 = l_Lake_Toml_loadToml___closed__8;
x_33 = l_Lake_Toml_loadToml___closed__11;
x_34 = l_Lake_Toml_loadToml___closed__12;
x_35 = l_Lake_Toml_loadToml___closed__15;
x_36 = l_Lake_Toml_loadToml___closed__16;
x_37 = l_Lake_Toml_loadToml___closed__18;
x_38 = l_Lake_Toml_loadToml___closed__19;
x_39 = l_Lake_Toml_loadToml___closed__21;
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_25);
x_41 = l_Lake_Toml_loadToml___closed__22;
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_33);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_36);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_40);
lean_ctor_set(x_42, 8, x_41);
x_43 = lean_st_mk_ref(x_42);
x_44 = l_Lake_Toml_loadToml___closed__23;
x_45 = lean_st_ref_get(x_44);
x_46 = lean_st_ref_get(x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = l_Lake_Toml_loadToml___closed__24;
x_50 = 0;
x_51 = lean_box(0);
x_52 = l_Lean_Parser_SyntaxStack_back(x_23);
lean_dec_ref(x_23);
x_53 = l_Lake_Toml_loadToml___closed__25;
x_54 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_12, x_53);
x_115 = l_Lean_Kernel_isDiagnosticsEnabled(x_47);
lean_dec_ref(x_47);
if (x_115 == 0)
{
if (x_54 == 0)
{
x_96 = x_25;
goto block_114;
}
else
{
x_96 = x_115;
goto block_114;
}
}
else
{
x_96 = x_54;
goto block_114;
}
block_95:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = l_Lake_Toml_loadToml___closed__26;
x_71 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_12, x_70);
x_72 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_12);
lean_ctor_set(x_72, 3, x_57);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_72, 5, x_58);
lean_ctor_set(x_72, 6, x_59);
lean_ctor_set(x_72, 7, x_60);
lean_ctor_set(x_72, 8, x_61);
lean_ctor_set(x_72, 9, x_62);
lean_ctor_set(x_72, 10, x_63);
lean_ctor_set(x_72, 11, x_64);
lean_ctor_set(x_72, 12, x_65);
lean_ctor_set(x_72, 13, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*14, x_54);
lean_ctor_set_uint8(x_72, sizeof(void*)*14 + 1, x_66);
x_73 = l_Lake_Toml_elabToml(x_52, x_72, x_68);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_st_ref_get(x_43);
lean_dec(x_43);
x_77 = lean_ctor_get(x_76, 6);
lean_inc_ref(x_77);
lean_dec(x_76);
x_78 = l_Lean_MessageLog_hasErrors(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
return x_73;
}
else
{
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_st_ref_get(x_43);
lean_dec(x_43);
x_81 = lean_ctor_get(x_80, 6);
lean_inc_ref(x_81);
lean_dec(x_80);
x_82 = l_Lean_MessageLog_hasErrors(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec_ref(x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_79);
return x_83;
}
else
{
lean_object* x_84; 
lean_dec(x_79);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_43);
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_73, 0);
x_87 = l_Lake_mkExceptionMessage(x_1, x_86);
x_88 = l_Lake_Toml_loadToml___closed__2;
x_89 = l_Lean_MessageLog_add(x_87, x_88);
lean_ctor_set(x_73, 0, x_89);
return x_73;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
lean_dec(x_73);
x_91 = l_Lake_mkExceptionMessage(x_1, x_90);
x_92 = l_Lake_Toml_loadToml___closed__2;
x_93 = l_Lean_MessageLog_add(x_91, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
block_114:
{
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_st_ref_take(x_43);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 5);
lean_dec(x_100);
x_101 = l_Lean_Kernel_enableDiag(x_99, x_54);
lean_ctor_set(x_97, 5, x_38);
lean_ctor_set(x_97, 0, x_101);
x_102 = lean_st_ref_set(x_43, x_97);
lean_inc(x_43);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_55 = x_10;
x_56 = x_11;
x_57 = x_30;
x_58 = x_48;
x_59 = x_13;
x_60 = x_12;
x_61 = x_30;
x_62 = x_49;
x_63 = x_13;
x_64 = x_31;
x_65 = x_51;
x_66 = x_50;
x_67 = x_45;
x_68 = x_43;
x_69 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
x_105 = lean_ctor_get(x_97, 2);
x_106 = lean_ctor_get(x_97, 3);
x_107 = lean_ctor_get(x_97, 4);
x_108 = lean_ctor_get(x_97, 6);
x_109 = lean_ctor_get(x_97, 7);
x_110 = lean_ctor_get(x_97, 8);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
x_111 = l_Lean_Kernel_enableDiag(x_103, x_54);
x_112 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_107);
lean_ctor_set(x_112, 5, x_38);
lean_ctor_set(x_112, 6, x_108);
lean_ctor_set(x_112, 7, x_109);
lean_ctor_set(x_112, 8, x_110);
x_113 = lean_st_ref_set(x_43, x_112);
lean_inc(x_43);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_55 = x_10;
x_56 = x_11;
x_57 = x_30;
x_58 = x_48;
x_59 = x_13;
x_60 = x_12;
x_61 = x_30;
x_62 = x_49;
x_63 = x_13;
x_64 = x_31;
x_65 = x_51;
x_66 = x_50;
x_67 = x_45;
x_68 = x_43;
x_69 = lean_box(0);
goto block_95;
}
}
else
{
lean_inc(x_43);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_55 = x_10;
x_56 = x_11;
x_57 = x_30;
x_58 = x_48;
x_59 = x_13;
x_60 = x_12;
x_61 = x_30;
x_62 = x_49;
x_63 = x_13;
x_64 = x_31;
x_65 = x_51;
x_66 = x_50;
x_67 = x_45;
x_68 = x_43;
x_69 = lean_box(0);
goto block_95;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_116 = lean_ctor_get(x_4, 0);
lean_inc(x_116);
lean_dec(x_4);
x_117 = l_Lake_Toml_loadToml___closed__0;
x_118 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_1, 0);
x_120 = lean_ctor_get(x_1, 1);
x_121 = lean_ctor_get(x_1, 2);
x_122 = lean_box(0);
x_123 = lean_box(0);
lean_inc(x_116);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_122);
x_125 = l_Lake_Toml_loadToml___closed__1;
x_126 = l_Lean_Parser_mkParserState(x_119);
lean_inc_ref(x_1);
x_127 = l_Lean_Parser_ParserFn_run(x_118, x_1, x_124, x_125, x_126);
x_128 = lean_ctor_get(x_127, 4);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_116);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = l_Lake_mkParserErrorMessage(x_1, x_127, x_129);
lean_dec_ref(x_127);
x_131 = l_Lake_Toml_loadToml___closed__2;
x_132 = l_Lean_MessageLog_add(x_130, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_128);
x_134 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_127, 2);
lean_inc(x_135);
x_136 = l_Lean_Parser_InputContext_atEnd(x_1, x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_134);
lean_dec(x_116);
x_137 = l_Lake_Toml_loadToml___closed__6;
x_138 = l_Lake_mkParserErrorMessage(x_1, x_127, x_137);
lean_dec_ref(x_127);
x_139 = l_Lake_Toml_loadToml___closed__2;
x_140 = l_Lean_MessageLog_add(x_138, x_139);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_200; uint8_t x_215; 
lean_dec_ref(x_127);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_Lake_Toml_loadToml___closed__7;
x_144 = l_Lake_Toml_loadToml___closed__8;
x_145 = l_Lake_Toml_loadToml___closed__11;
x_146 = l_Lake_Toml_loadToml___closed__12;
x_147 = l_Lake_Toml_loadToml___closed__15;
x_148 = l_Lake_Toml_loadToml___closed__16;
x_149 = l_Lake_Toml_loadToml___closed__18;
x_150 = l_Lake_Toml_loadToml___closed__19;
x_151 = l_Lake_Toml_loadToml___closed__21;
x_152 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_147);
lean_ctor_set_uint8(x_152, sizeof(void*)*3, x_136);
x_153 = l_Lake_Toml_loadToml___closed__22;
x_154 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_154, 0, x_116);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set(x_154, 4, x_148);
lean_ctor_set(x_154, 5, x_150);
lean_ctor_set(x_154, 6, x_151);
lean_ctor_set(x_154, 7, x_152);
lean_ctor_set(x_154, 8, x_153);
x_155 = lean_st_mk_ref(x_154);
x_156 = l_Lake_Toml_loadToml___closed__23;
x_157 = lean_st_ref_get(x_156);
x_158 = lean_st_ref_get(x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_159);
lean_dec(x_158);
x_160 = lean_box(0);
x_161 = l_Lake_Toml_loadToml___closed__24;
x_162 = 0;
x_163 = lean_box(0);
x_164 = l_Lean_Parser_SyntaxStack_back(x_134);
lean_dec_ref(x_134);
x_165 = l_Lake_Toml_loadToml___closed__25;
x_166 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_122, x_165);
x_215 = l_Lean_Kernel_isDiagnosticsEnabled(x_159);
lean_dec_ref(x_159);
if (x_215 == 0)
{
if (x_166 == 0)
{
x_200 = x_136;
goto block_214;
}
else
{
x_200 = x_215;
goto block_214;
}
}
else
{
x_200 = x_166;
goto block_214;
}
block_199:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = l_Lake_Toml_loadToml___closed__26;
x_183 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_122, x_182);
x_184 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_168);
lean_ctor_set(x_184, 2, x_122);
lean_ctor_set(x_184, 3, x_169);
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 5, x_170);
lean_ctor_set(x_184, 6, x_171);
lean_ctor_set(x_184, 7, x_172);
lean_ctor_set(x_184, 8, x_173);
lean_ctor_set(x_184, 9, x_174);
lean_ctor_set(x_184, 10, x_175);
lean_ctor_set(x_184, 11, x_176);
lean_ctor_set(x_184, 12, x_177);
lean_ctor_set(x_184, 13, x_179);
lean_ctor_set_uint8(x_184, sizeof(void*)*14, x_166);
lean_ctor_set_uint8(x_184, sizeof(void*)*14 + 1, x_178);
x_185 = l_Lake_Toml_elabToml(x_164, x_184, x_180);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec_ref(x_1);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = lean_st_ref_get(x_155);
lean_dec(x_155);
x_189 = lean_ctor_get(x_188, 6);
lean_inc_ref(x_189);
lean_dec(x_188);
x_190 = l_Lean_MessageLog_hasErrors(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec_ref(x_189);
if (lean_is_scalar(x_187)) {
 x_191 = lean_alloc_ctor(0, 1, 0);
} else {
 x_191 = x_187;
}
lean_ctor_set(x_191, 0, x_186);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_186);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_187;
 lean_ctor_set_tag(x_192, 1);
}
lean_ctor_set(x_192, 0, x_189);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_155);
x_193 = lean_ctor_get(x_185, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_194 = x_185;
} else {
 lean_dec_ref(x_185);
 x_194 = lean_box(0);
}
x_195 = l_Lake_mkExceptionMessage(x_1, x_193);
x_196 = l_Lake_Toml_loadToml___closed__2;
x_197 = l_Lean_MessageLog_add(x_195, x_196);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
block_214:
{
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_201 = lean_st_ref_take(x_155);
x_202 = lean_ctor_get(x_201, 0);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 2);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_201, 3);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_201, 4);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_201, 6);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_201, 7);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_201, 8);
lean_inc_ref(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 lean_ctor_release(x_201, 6);
 lean_ctor_release(x_201, 7);
 lean_ctor_release(x_201, 8);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Kernel_enableDiag(x_202, x_166);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 9, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_203);
lean_ctor_set(x_212, 2, x_204);
lean_ctor_set(x_212, 3, x_205);
lean_ctor_set(x_212, 4, x_206);
lean_ctor_set(x_212, 5, x_150);
lean_ctor_set(x_212, 6, x_207);
lean_ctor_set(x_212, 7, x_208);
lean_ctor_set(x_212, 8, x_209);
x_213 = lean_st_ref_set(x_155, x_212);
lean_inc(x_155);
lean_inc_ref(x_121);
lean_inc_ref(x_120);
x_167 = x_120;
x_168 = x_121;
x_169 = x_142;
x_170 = x_160;
x_171 = x_123;
x_172 = x_122;
x_173 = x_142;
x_174 = x_161;
x_175 = x_123;
x_176 = x_143;
x_177 = x_163;
x_178 = x_162;
x_179 = x_157;
x_180 = x_155;
x_181 = lean_box(0);
goto block_199;
}
else
{
lean_inc(x_155);
lean_inc_ref(x_121);
lean_inc_ref(x_120);
x_167 = x_120;
x_168 = x_121;
x_169 = x_142;
x_170 = x_160;
x_171 = x_123;
x_172 = x_122;
x_173 = x_142;
x_174 = x_161;
x_175 = x_123;
x_176 = x_143;
x_177 = x_163;
x_178 = x_162;
x_179 = x_157;
x_180 = x_155;
x_181 = lean_box(0);
goto block_199;
}
}
}
}
}
}
else
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_4);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_4, 0);
x_218 = l_Lake_Toml_loadToml___closed__28;
x_219 = lean_io_error_to_string(x_217);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l_Lean_MessageData_ofFormat(x_220);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = 2;
x_224 = l_Lake_mkMessageNoPos(x_1, x_222, x_223);
x_225 = l_Lake_Toml_loadToml___closed__2;
x_226 = l_Lean_MessageLog_add(x_224, x_225);
lean_ctor_set(x_4, 0, x_226);
return x_4;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_227 = lean_ctor_get(x_4, 0);
lean_inc(x_227);
lean_dec(x_4);
x_228 = l_Lake_Toml_loadToml___closed__28;
x_229 = lean_io_error_to_string(x_227);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = l_Lean_MessageData_ofFormat(x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_231);
x_233 = 2;
x_234 = l_Lake_mkMessageNoPos(x_1, x_232, x_233);
x_235 = l_Lake_Toml_loadToml___closed__2;
x_236 = l_Lean_MessageLog_add(x_234, x_235);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_loadToml(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin);
lean_object* initialize_Lake_Util_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin);
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
lean_mark_persistent(l_Lake_Toml_loadToml___closed__27);
l_Lake_Toml_loadToml___closed__28 = _init_l_Lake_Toml_loadToml___closed__28();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__28);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
