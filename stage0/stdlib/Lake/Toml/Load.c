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
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__28;
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
static lean_object* l_Lake_Toml_loadToml___closed__27;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_loadToml___closed__4;
x_2 = l_Lake_Toml_loadToml___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_empty;
return x_1;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lake_Toml_loadToml___closed__0;
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_box(0);
x_14 = lean_box(0);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lake_Toml_loadToml___closed__1;
x_17 = l_Lean_Parser_mkParserState(x_10);
lean_inc_ref(x_1);
x_18 = l_Lean_Parser_ParserFn_run(x_9, x_1, x_15, x_16, x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = l_Lean_Parser_InputContext_atEnd(x_1, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_20);
lean_dec(x_6);
x_23 = l_Lake_Toml_loadToml___closed__5;
x_24 = l_Lake_mkParserErrorMessage(x_1, x_18, x_23);
lean_dec_ref(x_18);
x_25 = l_Lake_Toml_loadToml___closed__6;
x_26 = l_Lean_MessageLog_add(x_24, x_25);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_93; uint8_t x_116; 
lean_dec_ref(x_18);
lean_free_object(x_4);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lake_Toml_loadToml___closed__7;
x_29 = l_Lake_Toml_loadToml___closed__8;
x_30 = l_Lake_Toml_loadToml___closed__11;
x_31 = l_Lake_Toml_loadToml___closed__12;
x_32 = l_Lake_Toml_loadToml___closed__15;
x_33 = l_Lake_Toml_loadToml___closed__16;
x_34 = l_Lake_Toml_loadToml___closed__18;
x_35 = l_Lake_Toml_loadToml___closed__19;
x_36 = l_Lake_Toml_loadToml___closed__21;
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_22);
x_38 = l_Lake_Toml_loadToml___closed__22;
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_37);
lean_ctor_set(x_39, 8, x_38);
x_40 = lean_st_mk_ref(x_39, x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lake_Toml_loadToml___closed__23;
x_44 = lean_st_ref_get(x_43, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_st_ref_get(x_41, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_50);
lean_dec(x_48);
x_51 = l_Lean_Parser_SyntaxStack_back(x_20);
lean_dec_ref(x_20);
x_52 = lean_box(0);
x_53 = l_Lake_Toml_loadToml___closed__24;
x_54 = 0;
x_55 = lean_box(0);
x_56 = l_Lake_Toml_loadToml___closed__25;
x_57 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_13, x_56);
x_116 = l_Lean_Kernel_isDiagnosticsEnabled(x_50);
lean_dec_ref(x_50);
if (x_116 == 0)
{
if (x_57 == 0)
{
x_93 = x_22;
goto block_115;
}
else
{
x_93 = x_116;
goto block_115;
}
}
else
{
x_93 = x_57;
goto block_115;
}
block_92:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lake_Toml_loadToml___closed__26;
x_61 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_13, x_60);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_62 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_62, 0, x_11);
lean_ctor_set(x_62, 1, x_12);
lean_ctor_set(x_62, 2, x_13);
lean_ctor_set(x_62, 3, x_27);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_52);
lean_ctor_set(x_62, 6, x_14);
lean_ctor_set(x_62, 7, x_13);
lean_ctor_set(x_62, 8, x_27);
lean_ctor_set(x_62, 9, x_53);
lean_ctor_set(x_62, 10, x_14);
lean_ctor_set(x_62, 11, x_28);
lean_ctor_set(x_62, 12, x_55);
lean_ctor_set(x_62, 13, x_45);
lean_ctor_set_uint8(x_62, sizeof(void*)*14, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*14 + 1, x_54);
x_63 = l_Lake_Toml_elabToml(x_51, x_62, x_58, x_59);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_st_ref_get(x_41, x_66);
lean_dec(x_41);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 6);
lean_inc_ref(x_70);
lean_dec(x_68);
x_71 = l_Lean_MessageLog_hasErrors(x_70);
if (x_71 == 0)
{
lean_dec_ref(x_70);
lean_ctor_set(x_63, 1, x_69);
return x_63;
}
else
{
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 1, x_69);
lean_ctor_set(x_63, 0, x_70);
return x_63;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = lean_st_ref_get(x_41, x_73);
lean_dec(x_41);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 6);
lean_inc_ref(x_77);
lean_dec(x_75);
x_78 = l_Lean_MessageLog_hasErrors(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec_ref(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; 
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_41);
x_81 = !lean_is_exclusive(x_63);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_63, 0);
x_83 = l_Lake_mkExceptionMessage(x_1, x_82);
x_84 = l_Lake_Toml_loadToml___closed__6;
x_85 = l_Lean_MessageLog_add(x_83, x_84);
lean_ctor_set(x_63, 0, x_85);
return x_63;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_63);
x_88 = l_Lake_mkExceptionMessage(x_1, x_86);
x_89 = l_Lake_Toml_loadToml___closed__6;
x_90 = l_Lean_MessageLog_add(x_88, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
}
block_115:
{
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_st_ref_take(x_41, x_49);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 5);
lean_dec(x_99);
x_100 = l_Lean_Kernel_enableDiag(x_98, x_57);
lean_ctor_set(x_95, 5, x_35);
lean_ctor_set(x_95, 0, x_100);
x_101 = lean_st_ref_set(x_41, x_95, x_96);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
lean_inc(x_41);
x_58 = x_41;
x_59 = x_102;
goto block_92;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_103 = lean_ctor_get(x_95, 0);
x_104 = lean_ctor_get(x_95, 1);
x_105 = lean_ctor_get(x_95, 2);
x_106 = lean_ctor_get(x_95, 3);
x_107 = lean_ctor_get(x_95, 4);
x_108 = lean_ctor_get(x_95, 6);
x_109 = lean_ctor_get(x_95, 7);
x_110 = lean_ctor_get(x_95, 8);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_95);
x_111 = l_Lean_Kernel_enableDiag(x_103, x_57);
x_112 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_107);
lean_ctor_set(x_112, 5, x_35);
lean_ctor_set(x_112, 6, x_108);
lean_ctor_set(x_112, 7, x_109);
lean_ctor_set(x_112, 8, x_110);
x_113 = lean_st_ref_set(x_41, x_112, x_96);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
lean_inc(x_41);
x_58 = x_41;
x_59 = x_114;
goto block_92;
}
}
else
{
lean_inc(x_41);
x_58 = x_41;
x_59 = x_49;
goto block_92;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_6);
x_117 = lean_ctor_get(x_19, 0);
lean_inc(x_117);
lean_dec_ref(x_19);
x_118 = l_Lake_mkParserErrorMessage(x_1, x_18, x_117);
lean_dec_ref(x_18);
x_119 = l_Lake_Toml_loadToml___closed__6;
x_120 = l_Lean_MessageLog_add(x_118, x_119);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_120);
return x_4;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = l_Lake_Toml_loadToml___closed__0;
x_124 = lean_ctor_get(x_123, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_1, 0);
x_126 = lean_ctor_get(x_1, 1);
x_127 = lean_ctor_get(x_1, 2);
x_128 = lean_box(0);
x_129 = lean_box(0);
lean_inc(x_121);
x_130 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_128);
x_131 = l_Lake_Toml_loadToml___closed__1;
x_132 = l_Lean_Parser_mkParserState(x_125);
lean_inc_ref(x_1);
x_133 = l_Lean_Parser_ParserFn_run(x_124, x_1, x_130, x_131, x_132);
x_134 = lean_ctor_get(x_133, 4);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_133, 2);
lean_inc(x_136);
x_137 = l_Lean_Parser_InputContext_atEnd(x_1, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_135);
lean_dec(x_121);
x_138 = l_Lake_Toml_loadToml___closed__5;
x_139 = l_Lake_mkParserErrorMessage(x_1, x_133, x_138);
lean_dec_ref(x_133);
x_140 = l_Lake_Toml_loadToml___closed__6;
x_141 = l_Lean_MessageLog_add(x_139, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_122);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_198; uint8_t x_216; 
lean_dec_ref(x_133);
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Lake_Toml_loadToml___closed__7;
x_145 = l_Lake_Toml_loadToml___closed__8;
x_146 = l_Lake_Toml_loadToml___closed__11;
x_147 = l_Lake_Toml_loadToml___closed__12;
x_148 = l_Lake_Toml_loadToml___closed__15;
x_149 = l_Lake_Toml_loadToml___closed__16;
x_150 = l_Lake_Toml_loadToml___closed__18;
x_151 = l_Lake_Toml_loadToml___closed__19;
x_152 = l_Lake_Toml_loadToml___closed__21;
x_153 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_148);
lean_ctor_set_uint8(x_153, sizeof(void*)*3, x_137);
x_154 = l_Lake_Toml_loadToml___closed__22;
x_155 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_155, 0, x_121);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set(x_155, 4, x_149);
lean_ctor_set(x_155, 5, x_151);
lean_ctor_set(x_155, 6, x_152);
lean_ctor_set(x_155, 7, x_153);
lean_ctor_set(x_155, 8, x_154);
x_156 = lean_st_mk_ref(x_155, x_122);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = l_Lake_Toml_loadToml___closed__23;
x_160 = lean_st_ref_get(x_159, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_st_ref_get(x_157, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_166);
lean_dec(x_164);
x_167 = l_Lean_Parser_SyntaxStack_back(x_135);
lean_dec_ref(x_135);
x_168 = lean_box(0);
x_169 = l_Lake_Toml_loadToml___closed__24;
x_170 = 0;
x_171 = lean_box(0);
x_172 = l_Lake_Toml_loadToml___closed__25;
x_173 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_128, x_172);
x_216 = l_Lean_Kernel_isDiagnosticsEnabled(x_166);
lean_dec_ref(x_166);
if (x_216 == 0)
{
if (x_173 == 0)
{
x_198 = x_137;
goto block_215;
}
else
{
x_198 = x_216;
goto block_215;
}
}
else
{
x_198 = x_173;
goto block_215;
}
block_197:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = l_Lake_Toml_loadToml___closed__26;
x_177 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_128, x_176);
lean_inc_ref(x_127);
lean_inc_ref(x_126);
x_178 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_178, 0, x_126);
lean_ctor_set(x_178, 1, x_127);
lean_ctor_set(x_178, 2, x_128);
lean_ctor_set(x_178, 3, x_143);
lean_ctor_set(x_178, 4, x_177);
lean_ctor_set(x_178, 5, x_168);
lean_ctor_set(x_178, 6, x_129);
lean_ctor_set(x_178, 7, x_128);
lean_ctor_set(x_178, 8, x_143);
lean_ctor_set(x_178, 9, x_169);
lean_ctor_set(x_178, 10, x_129);
lean_ctor_set(x_178, 11, x_144);
lean_ctor_set(x_178, 12, x_171);
lean_ctor_set(x_178, 13, x_161);
lean_ctor_set_uint8(x_178, sizeof(void*)*14, x_173);
lean_ctor_set_uint8(x_178, sizeof(void*)*14 + 1, x_170);
x_179 = l_Lake_Toml_elabToml(x_167, x_178, x_174, x_175);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_st_ref_get(x_157, x_181);
lean_dec(x_157);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = lean_ctor_get(x_184, 6);
lean_inc_ref(x_186);
lean_dec(x_184);
x_187 = l_Lean_MessageLog_hasErrors(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec_ref(x_186);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_180);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
else
{
lean_object* x_189; 
lean_dec(x_180);
if (lean_is_scalar(x_182)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_182;
 lean_ctor_set_tag(x_189, 1);
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_185);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_157);
x_190 = lean_ctor_get(x_179, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_179, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_192 = x_179;
} else {
 lean_dec_ref(x_179);
 x_192 = lean_box(0);
}
x_193 = l_Lake_mkExceptionMessage(x_1, x_190);
x_194 = l_Lake_Toml_loadToml___closed__6;
x_195 = l_Lean_MessageLog_add(x_193, x_194);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
}
block_215:
{
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_199 = lean_st_ref_take(x_157, x_165);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 2);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_200, 3);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_200, 4);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_200, 6);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_200, 7);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_200, 8);
lean_inc_ref(x_209);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 lean_ctor_release(x_200, 6);
 lean_ctor_release(x_200, 7);
 lean_ctor_release(x_200, 8);
 x_210 = x_200;
} else {
 lean_dec_ref(x_200);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Kernel_enableDiag(x_202, x_173);
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
lean_ctor_set(x_212, 5, x_151);
lean_ctor_set(x_212, 6, x_207);
lean_ctor_set(x_212, 7, x_208);
lean_ctor_set(x_212, 8, x_209);
x_213 = lean_st_ref_set(x_157, x_212, x_201);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec_ref(x_213);
lean_inc(x_157);
x_174 = x_157;
x_175 = x_214;
goto block_197;
}
else
{
lean_inc(x_157);
x_174 = x_157;
x_175 = x_165;
goto block_197;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_121);
x_217 = lean_ctor_get(x_134, 0);
lean_inc(x_217);
lean_dec_ref(x_134);
x_218 = l_Lake_mkParserErrorMessage(x_1, x_133, x_217);
lean_dec_ref(x_133);
x_219 = l_Lake_Toml_loadToml___closed__6;
x_220 = l_Lean_MessageLog_add(x_218, x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_122);
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
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_223 = lean_ctor_get(x_4, 0);
x_224 = l_Lake_Toml_loadToml___closed__28;
x_225 = lean_io_error_to_string(x_223);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l_Lean_MessageData_ofFormat(x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = 2;
x_230 = l_Lake_mkMessageNoPos(x_1, x_228, x_229);
x_231 = l_Lake_Toml_loadToml___closed__6;
x_232 = l_Lean_MessageLog_add(x_230, x_231);
lean_ctor_set(x_4, 0, x_232);
return x_4;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_233 = lean_ctor_get(x_4, 0);
x_234 = lean_ctor_get(x_4, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_4);
x_235 = l_Lake_Toml_loadToml___closed__28;
x_236 = lean_io_error_to_string(x_233);
x_237 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = l_Lean_MessageData_ofFormat(x_237);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_235);
lean_ctor_set(x_239, 1, x_238);
x_240 = 2;
x_241 = l_Lake_mkMessageNoPos(x_1, x_239, x_240);
x_242 = l_Lake_Toml_loadToml___closed__6;
x_243 = l_Lean_MessageLog_add(x_241, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_234);
return x_244;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
lean_mark_persistent(l_Lake_Toml_loadToml___closed__27);
l_Lake_Toml_loadToml___closed__28 = _init_l_Lake_Toml_loadToml___closed__28();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__28);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
